"""Static interface elaboration; execution still uses ordinary imported calls."""

import ast
import copy
from dataclasses import dataclass, replace

from .frontend import ClassInfo, Function
from .interfaces import check_binding, interface_namespace
from .project import ProjectError, Symbol
from .source_types import sequence_element, sequence_type


@dataclass
class InterfaceSlot:
    field: str
    namespace: str
    local_name: str
    info: object


@dataclass
class Environment:
    target: object
    codes: dict
    facts: dict


def prepare_interfaces(project, owner, infos, names, classes, origins, functions, calls, *, members=()):
    from .modular import ImportedCall, namespace
    available = set(project.transitive_dependencies(owner)) | {owner.name} | set(members)
    for index, (symbol, info) in enumerate(infos.items()):
        if symbol.module not in available:
            continue
        names.setdefault(symbol, symbol.name if symbol.module == owner.name else
                         '_a2l_import_interface_' + str(index) + '_' + symbol.name)
        origins[names[symbol]] = symbol

    canonical = {origin.canonical_name: local for local, origin in origins.items()}

    def translate(typ):
        element = sequence_element(typ)
        if element is not None:
            return sequence_type(translate(element))
        nullable = typ.endswith('?')
        base = typ.rstrip('?')
        return canonical.get(base, base) + ('?' if nullable else '')

    for symbol, info in infos.items():
        if symbol.module not in available:
            continue
        local = names[symbol]
        definition = ClassInfo(local, is_interface=True)
        classes[local] = definition
        for method, signature in info.methods.items():
            name = local + '_' + method
            node = copy.deepcopy(signature.node)
            node.name = name
            parameters = [('self', local)] + [(arg, translate(typ)) for arg, typ in signature.parameters]
            function = Function(node, parameters, translate(signature.return_type), dict(parameters),
                                classes=classes, class_name=local, method_name=method)
            functions[name] = function
            definition.methods[method] = name
            calls[name] = ImportedCall(function, interface_namespace(info),
                                       symbol.name + '_' + method, '', len(info.methods), symbol.module,
                                       interface_code='pending')


def resolve_interfaces(owner, module, all_functions, all_calls, compiled, infos):
    """Select dependencies and method dictionaries from checked source types.

    A module instance uses one implementation of each declared interface. Calling
    it twice with different concrete classes creates two small environment values,
    while sharing the independently compiled body and its analysis.
    """
    from .modular import namespace

    def fail(node, message):
        raise ProjectError(message, owner.path, getattr(node, 'lineno', 1), getattr(node, 'col_offset', 0) + 1)

    def interface_type(typ, node=None):
        element = sequence_element(typ)
        if element is not None:
            if interface_type(element, node):
                fail(node or owner.tree, 'Sequences of abstract interface references are not supported yet; use concrete element classes.')
            return None
        origin = module.class_origins.get(typ.rstrip('?'))
        return origin if origin and origin.kind == 'interface' else None

    needed = set()
    field_annotations = {
        (declaration.name, member.target.id): member.annotation
        for declaration in owner.tree.body if isinstance(declaration, ast.ClassDef)
        for member in declaration.body
        if isinstance(member, ast.AnnAssign) and isinstance(member.target, ast.Name)
    }
    for definition in module.classes.values():
        for field, typ in definition.fields.items():
            annotation = field_annotations.get((definition.name, field), owner.tree)
            if interface_type(typ, annotation):
                fail(annotation, 'Abstract interface references are not supported in object fields yet; pass them as function parameters.')
    for function in module.functions.values():
        for typ in [function.return_type, *function.variables.values(), *function.expression_types.values()]:
            origin = interface_type(typ, function.node)
            if origin:
                needed.add(origin)
    for origin in sorted(needed, key=lambda item: item.canonical_name):
        local = next(name for name, symbol in module.class_origins.items() if symbol == origin)
        field = origin.name
        suffix = 0
        while any(slot.field == field for slot in module.dependencies.values()):
            suffix += 1
            field = origin.name + '_' + str(suffix)
        module.dependencies[origin] = InterfaceSlot(field, interface_namespace(infos[origin]),
                                                   local, infos[origin])

    bindings, environments, instances = {}, {}, {}
    used_calls = {}
    for function in module.functions.values():
        # Concrete references may widen to an interface only at imported calls,
        # where the implementation is selected statically. Stored interface
        # values carry no implementation identity, so widening them is rejected.
        permitted_coercions = set()
        for expression in ast.walk(function.node):
            if not isinstance(expression, ast.Call):
                continue
            target_call = all_calls.get(getattr(expression, 'resolved_name', None))
            if target_call and not target_call.interface_code and compiled[target_call.module].dependencies:
                permitted_coercions.update(id(arg) for arg in expression.args)
        for expression in ast.walk(function.node):
            expected = getattr(expression, 'expected_type', None)
            actual = function.expression_types.get(id(expression))
            if (expected and actual != expected and interface_type(expected, expression)
                    and id(expression) not in permitted_coercions):
                fail(expression, 'Pass concrete objects directly to an imported generic function; storing an interface conversion is not supported yet.')
        for node in ast.walk(function.node):
            if not isinstance(node, ast.Call):
                continue
            resolved = getattr(node, 'resolved_name', None)
            target = all_functions.get(resolved)
            if target is None:
                continue
            args = ([node.receiver] if getattr(node, 'receiver', None) is not None else []) + node.args
            code = all_calls.get(resolved)
            if code is None:
                for arg, (_, expected) in zip(args, target.parameters):
                    actual = function.expression_types[id(arg)]
                    if interface_type(expected, arg) and actual != expected:
                        fail(node, 'Instantiate a generic algorithm from another module; local calls keep the current interface implementation.')
                continue
            if code.interface_code:
                origin = module.class_origins[code.function.class_name]
                slot = module.dependencies[origin]
                used_calls[resolved] = replace(code, frame='interface_' + slot.field,
                                               interface_code='dependencies.«' + slot.field + '»')
                continue
            dependency = compiled[code.module]
            if not dependency.dependencies:
                used_calls[resolved] = code
                continue
            if interface_type(target.return_type, node):
                fail(node, 'Returning an abstract interface from an instantiated call is not supported yet; return ordinary values or a concrete class.')
            selected = {}
            for arg, (_, expected) in zip(args, target.parameters):
                origin = interface_type(expected, arg)
                if origin is None:
                    continue
                actual = function.expression_types[id(arg)].rstrip('?')
                previous = selected.setdefault(origin, actual)
                if previous != actual:
                    fail(node, 'Arguments for interface %s must use the same implementation in one call.' % origin.name)
            codes, facts = {}, {}
            for origin, target_slot in dependency.dependencies.items():
                actual = selected.get(origin)
                actual_origin = module.class_origins.get(actual) if actual else origin
                if actual_origin == origin and origin in module.dependencies:
                    slot = module.dependencies[origin]
                    codes[target_slot.field] = 'dependencies.«' + slot.field + '»'
                    facts[target_slot.field] = 'facts.«' + slot.field + '»'
                    continue
                if actual_origin is None or actual_origin.kind != 'class':
                    fail(node, 'Cannot infer implementation of interface %s; supply an object parameter.' % origin.name)
                if actual_origin.module in module.group_members:
                    fail(node, 'Import concrete interface implementations from outside the recursive compilation group.')
                if actual_origin.module == owner.name:
                    fail(node, 'Import concrete interface implementations from a separate module.')
                backend = compiled[actual_origin.module]
                if backend.dependencies:
                    fail(node, 'Binding a class with abstract dependencies is not supported yet; first export a concrete wrapper.')
                key = (origin, actual_origin)
                if key not in bindings:
                    binding = check_binding(infos[origin], backend, actual_origin.name, owner=owner, node=node)
                    stem = actual_origin.name + '_as_' + origin.name
                    name, suffix = stem, 0
                    while name in module.bindings:
                        suffix += 1
                        name = stem + '_' + str(suffix)
                    module.bindings[name] = binding
                    bindings[key] = name
                name = bindings[key]
                codes[target_slot.field] = name
                facts[target_slot.field] = name + '_facts'
            key = (code.module, tuple(codes.items()))
            if key not in environments:
                name = 'use_' + code.module.replace('.', '_') + '_' + str(len(environments))
                module.environments[name] = Environment(dependency, codes, facts)
                environments[key] = name
            env = environments[key]
            instance = (resolved, env)
            if instance not in instances:
                local = resolved + '_instance_' + str(len(instances))
                environment = '(' + env + ' dependencies)' if module.dependencies else env
                environment_facts = '(' + env + '_facts dependencies facts)' if module.dependencies else env + '_facts'
                used_calls[local] = replace(code, frame=code.frame + '_' + env,
                    environment=environment, environment_facts=environment_facts)
                instances[instance] = local
            node.resolved_name = instances[instance]
    module.imports = used_calls
