"""Compile a strongly connected source group using ordinary local call rules.

Only source modules in the cycle share execution types. Public facade modules
retain their source namespaces and import paths; all other dependencies keep
their existing independently checked transitions.
"""

import ast
import copy
import hashlib
import re
from dataclasses import replace

from .compiler import Lowerer, assign_points, validate_generated_names
from .frontend import CompileError, parse_program
from .project import ProjectError, SourceModule, Symbol
from .publication import credit_generated
from .public_names import function_namespace, identifier, interface_entries
from .source_types import sequence_element, sequence_type


def _translate_type(typ, names):
    element = sequence_element(typ)
    if element is not None:
        return sequence_type(_translate_type(element, names))
    base = typ.rstrip('?')
    return names.get(base, base) + ('?' if typ.endswith('?') else '')


def _alias(name, target, *, pattern=False):
    return ('@[match_pattern] ' if pattern else '') + 'abbrev ' + name + ' := @' + target


def _facade(owner, implementation, function_names, class_names):
    """Expose the original source names without duplicating transition rules."""
    from .modular import CompiledModule, lean_module, namespace
    from .objects import emit_classes

    own_classes = {internal: source for source, internal in class_names.items()}
    own_functions = {internal: source for source, internal in function_names.items()}
    translate = lambda typ: _translate_type(typ, own_classes)
    classes, origins = {}, {}
    for internal, definition in implementation.classes.items():
        name = own_classes.get(internal, internal)
        classes[name] = replace(definition, name=name,
            fields={field: translate(typ) for field, typ in definition.fields.items()},
            methods={method: own_functions.get(target, target) for method, target in definition.methods.items()},
            constructor=own_functions.get(definition.constructor, definition.constructor),
            imported_from=implementation.namespace, imported_name=internal)
        origins[name] = implementation.class_origins[internal]
    functions = {}
    for name, internal in function_names.items():
        original = implementation.functions[internal]
        node = copy.copy(original.node)
        node.name = name
        points = copy.deepcopy(original.points)
        for point in points.values():
            for variable in point['variables']:
                variable['type'] = translate(variable['type'])
        function = replace(original, node=node,
            parameters=[(name, translate(typ)) for name, typ in original.parameters],
            return_type=translate(original.return_type),
            variables={name: translate(typ) for name, typ in original.variables.items()},
            expression_types={key: translate(typ) for key, typ in original.expression_types.items()},
            classes=classes, points=points,
            class_name=own_classes.get(original.class_name, original.class_name),
            constructor_for=own_classes.get(original.constructor_for, original.constructor_for))
        for point in points.values():
            point['relation'] = function_namespace(function) + '.At.' + identifier(point['name'])
        functions[name] = function
    module = CompiledModule(owner.name, namespace(owner.name), lean_module(owner.name), '',
        lean_module(owner.name, 'Points'), '', functions, classes, origins,
        {name: implementation.lowered[internal] for name, internal in function_names.items()},
        {}, implementation.clocks, implementation=implementation,
        implementation_names=function_names, dependencies=implementation.dependencies,
        group_members=implementation.group_members)
    module.facts_module = lean_module(owner.name, 'Facts')
    source = implementation.namespace
    generated = source + '.Algo2LeanGenerated.'
    header = ['import ' + implementation.lean_module, '',
        '-- Independently compiled module; execution is shared by recursive imports.',
        '-- Shared transition rules: ' + implementation.lean_module,
        'namespace ' + module.namespace, '', 'open _root_.Algo2LeanGenerated', '']
    if implementation.dependencies:
        header += [_alias('Dependencies', source + '.Dependencies'), '']
    lines = header + ['namespace Algo2LeanGenerated', '']
    emit_classes(lines, classes)
    for name in ('Frame', 'Result', 'Configuration', 'Stack', 'Transcript', 'Step', 'terminal'):
        lines.append(_alias(name, generated + name))
    for name, internal in function_names.items():
        lines += [_alias('State_' + name, generated + 'State_' + internal),
                  _alias('Frame.fn_' + name, generated + 'Frame.fn_' + internal, pattern=True),
                  _alias('Result.fn_' + name, generated + 'Result.fn_' + internal, pattern=True)]
    lines += ['', 'end Algo2LeanGenerated', '', 'open Algo2LeanGenerated', '']
    points = ['import ' + module.lean_module, 'import ' + implementation.points_module,
        '', '-- Named locations are independent of the compiled module body.',
        'namespace ' + module.namespace, '', 'open _root_.Algo2LeanGenerated Algo2LeanGenerated', '']
    facts = ['import ' + module.lean_module, 'import ' + implementation.facts_module,
        '', '-- Optional proof certificate; execution remains the generated Step relation.',
        'namespace ' + module.namespace, '', 'open _root_.Algo2LeanGenerated Algo2LeanGenerated', '']
    if implementation.dependencies:
        facts.append(_alias('DependencyFacts', source + '.DependencyFacts'))
    facts += ['namespace Algo2LeanGenerated']
    for name in ('next', 'step_next', 'deterministic'):
        facts.append(_alias(name, generated + name))
    facts += ['end Algo2LeanGenerated', '']
    for name, internal in function_names.items():
        function = functions[name]
        original = implementation.functions[internal]
        prefix = source + '.' + function_namespace(original)
        public = function_namespace(function)
        lines.append(_alias('entry_' + name, source + '.entry_' + internal))
        for entry in interface_entries(function, bool(implementation.clocks) or bool(implementation.dependencies),
                                       dependencies=bool(implementation.dependencies), facts=True):
            suffix = entry['name'][len(public):]
            destination = points if entry['file_kind'] == 'points' else facts if entry['file_kind'] == 'facts' else lines
            if suffix in {'.Call.run', '.ReturnsWithCost.returns', '.Returns.withCost', '.Run.eq_of_call'}:
                arguments = ' '.join(argument['name'] for argument in entry['arguments'])
                destination.append('theorem ' + entry['signature'] + ' :=\n  @' + prefix + suffix + ' ' + arguments)
            else:
                destination.append(_alias(entry['name'], prefix + suffix))
    for content in (lines, points, facts):
        content += ['', 'end ' + module.namespace, '']
    module.lean, module.points_lean, module.facts_lean = map(credit_generated,
        ('\n'.join(lines), '\n'.join(points), '\n'.join(facts)))
    return module


def compile_group(result, members, interfaces):
    """Lower one cyclic group, then publish its per-source public interfaces."""
    from .interfaces import emit_interface
    from .modular import CompiledModule, _emit, _imports, _public_facts, _tree, lean_module, namespace
    from .module_facts import emit_facts
    from .module_interfaces import prepare_interfaces, resolve_interfaces

    project = result.project
    members = tuple(sorted(members))
    # Dependency traversal depends on the selected entry. Interface declarations
    # need a stable order so the shared execution and its facades do not.
    interfaces = dict(sorted(interfaces.items(), key=lambda item: item[0].canonical_name))
    digest = hashlib.sha256('\0'.join(members).encode()).hexdigest()[:16]
    group_name = '_a2l_groups.G' + digest
    owners = [project.modules[name] for name in members]
    dependencies = tuple(sorted({dependency for owner in owners for dependency in owner.dependencies
                                 if dependency not in members}))
    synthetic = SourceModule(group_name, owners[0].path, '', ast.Module(body=[], type_ignores=[]), dependencies)
    names, classes, origins, external, calls = _imports(project, synthetic, result.modules)
    function_names, class_names = {name: {} for name in members}, {name: {} for name in members}
    for index, owner in enumerate(owners):
        for declaration in owner.tree.body:
            if not isinstance(declaration, (ast.FunctionDef, ast.ClassDef)):
                continue
            symbol = owner.bindings[declaration.name]
            internal = '_a2l_group_%d_%s' % (index, declaration.name)
            names[symbol] = internal
            synthetic.bindings[internal] = symbol
            if isinstance(declaration, ast.ClassDef):
                class_names[owner.name][declaration.name] = internal
                origins[internal] = symbol
            else:
                function_names[owner.name][declaration.name] = internal
    prepare_interfaces(project, synthetic, interfaces, names, classes, origins, external, calls, members=members)
    locations = []
    offset = 0
    for owner in owners:
        tree = _tree(owner, names)
        body = []
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.ClassDef)):
                symbol = owner.bindings[node.name]
                node.name = names[symbol]
                if symbol.kind == 'interface':
                    continue
            ast.increment_lineno(node, offset)
            body.append(node)
        count = len(owner.source.splitlines()) + 1
        locations.append((offset, offset + count, owner))
        offset += count
        synthetic.source += owner.source + ('' if owner.source.endswith('\n') else '\n') + '\n'
        synthetic.tree.body.extend(body)

    def location(line):
        return next(((start, owner) for start, end, owner in locations if start < line <= end), (0, owners[0]))

    def source_message(message):
        public = {internal: symbol.canonical_name for symbol, internal in names.items()}
        for owner in owners:
            for source, internal in function_names[owner.name].items():
                # Methods use source class/member notation in diagnostics, even
                # though the frontend represents them as ordinary functions.
                method = next((cls + '.' + source[len(cls) + 1:]
                               for cls in class_names[owner.name]
                               if source.startswith(cls + '_')), source)
                public.setdefault(internal, owner.name + '.' + method)
        if not public:
            return message
        identifiers = '|'.join(re.escape(name) for name in sorted(public, key=len, reverse=True))
        return re.sub(r'(?<![A-Za-z_0-9])(?:' + identifiers + r')(?![A-Za-z_0-9])',
                      lambda match: public[match.group()], message)

    try:
        if synthetic.tree.body:
            all_functions, classes = parse_program(synthetic.tree, imported_functions=external, imported_classes=classes)
            functions = {name: function for name, function in all_functions.items() if name not in external}
        else:
            all_functions, functions = external, {}
        for owner in owners:
            for source, internal in class_names[owner.name].items():
                definition = classes[internal]
                definition.runtime_tag = owner.name + '.' + source
                if not definition.is_interface:
                    function_names[owner.name][source] = definition.constructor
                    for method, target in definition.methods.items():
                        function_names[owner.name][source + '_' + method] = target
        assign_points(functions, synthetic.source)
        if all_functions:
            validate_generated_names(all_functions)
        clocks = tuple(sorted({clock for function in all_functions.values() for clock in function.clocks}))
        compiled = CompiledModule(group_name, namespace(group_name), lean_module(group_name), '',
            lean_module(group_name, 'Points'), '', functions, classes, origins, {}, {}, clocks,
            group_members=members)
        resolve_interfaces(synthetic, compiled, all_functions, calls, result.modules, interfaces)
        compiled.lowered = {name: Lowerer(function) for name, function in functions.items()}
        # Checking and lowering use disjoint source line ranges. Once those
        # finish, restore source coordinates for editor metadata and observations.
        visited = set()
        for function in functions.values():
            for node in ast.walk(function.node):
                if id(node) in visited:
                    continue
                visited.add(id(node))
                if hasattr(node, 'lineno'):
                    start, _ = location(node.lineno)
                    node.lineno -= start
                    if getattr(node, 'end_lineno', None) is not None:
                        node.end_lineno -= start
            for point in function.points.values():
                start, _ = location(point['line'])
                point['line'] -= start
                point['end_line'] -= start
        compiled.lean, compiled.points_lean = _emit(synthetic, compiled, [])
        declarations = [info for symbol, info in interfaces.items() if symbol.module in members]
        if declarations:
            insertion = '\n'.join('namespace ' + namespace(info.module) + '\nopen _root_.Algo2LeanGenerated\n' +
                emit_interface(info) + '\nend ' + namespace(info.module) for info in declarations)
            marker = 'namespace ' + compiled.namespace
            compiled.lean = compiled.lean.replace(marker, insertion + '\n\n' + marker, 1)
            if 'import Algo2LeanLib.Interface\n' not in compiled.lean:
                compiled.lean = compiled.lean.replace('import Algo2LeanLib.Modules\n',
                    'import Algo2LeanLib.Modules\nimport Algo2LeanLib.Interface\n', 1)
        compiled.facts_module = lean_module(group_name, 'Facts')
        compiled.facts_lean = credit_generated(emit_facts(compiled) + _public_facts(compiled))
        result.implementation_modules[group_name] = compiled
        for owner in owners:
            result.modules[owner.name] = _facade(owner, compiled, function_names[owner.name], class_names[owner.name])
    except ProjectError as error:
        if error.path != str(synthetic.path):
            raise ProjectError(source_message(error.message), error.path, error.line, error.column) from None
        start, owner = location(error.line)
        raise ProjectError(source_message(error.message), owner.path, error.line - start, error.column) from None
    except CompileError as error:
        start, owner = location(error.line)
        raise ProjectError(source_message(error.message), owner.path, error.line - start, error.column) from None
