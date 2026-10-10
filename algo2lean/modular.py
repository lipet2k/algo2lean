"""Separate compilation: imports refer to existing typed modules and proofs.

The local language checker/lowerer is shared with single-file compilation.
Only names, external call boundaries, and the module namespace differ.
"""

import ast
import copy
from dataclasses import dataclass, field
from pathlib import Path

from .compiler import Lowerer, assign_points, validate_generated_names
from .emitter import (constructor, emit_points, emit_public, emit_step, frame,
                      input_values, state_value, tuple_type)
from .frontend import ClassInfo, CompileError, Function, parse_program
from .objects import (collection_types, default_value, emit_classes,
                      emit_collections, raw_type)
from .project import Project, ProjectError, Symbol, load_project
from .source_types import sequence_element, sequence_type
from .publication import credit_generated


def namespace(name):
    return "Algo." + ".".join("«%s»" % part for part in name.split("."))


def lean_module(name, part="Generated"):
    return "Algo." + name + "." + part


@dataclass
class ImportedCall:
    function: Function
    namespace: str
    name: str
    frame: str
    result_count: int
    module: str
    environment: str = ""
    interface_code: str = ""
    environment_facts: str = ""

    def source(self, member):
        if self.interface_code:
            if member == "Result":
                return self.namespace + ".Result"
            if member in {"next", "step_next"}:
                return self.interface_code.replace("dependencies.", "facts.") + "." + member
            if member in {"Stack", "Configuration"}:
                kind = "Stack" if member == "Stack" else "Config Heap"
                return "(Algo2LeanCore.%s %s.Frame %s.Result)" % (kind, self.interface_code, self.namespace)
            return self.interface_code + "." + member
        name = self.namespace + ".Algo2LeanGenerated." + member
        if self.environment and member != "Result":
            name += " " + self.environment
            if member in {"next", "step_next"}:
                name += " " + self.environment_facts
            return "(" + name + ")"
        return name

    source_frame = property(lambda self: self.source("Frame"))
    source_stack = property(lambda self: self.source("Stack"))
    source_result = property(lambda self: self.source("Result"))
    source_config = property(lambda self: self.source("Configuration"))
    source_step = property(lambda self: self.source("Step"))
    source_terminal = property(lambda self: self.source("terminal"))
    source_next = property(lambda self: self.source("next"))
    source_step_next = property(lambda self: self.source("step_next"))

    @property
    def entry(self):
        if self.interface_code:
            return self.interface_code + ".entry_" + self.name
        return self.namespace + ".entry_" + self.name + (" " + self.environment if self.environment else "")


@dataclass
class CompiledModule:
    name: str
    namespace: str
    lean_module: str
    lean: str
    points_module: str
    points_lean: str
    functions: dict
    classes: dict
    class_origins: dict
    lowered: dict
    imports: dict
    clocks: tuple
    facts_module: str = ""
    facts_lean: str = ""
    dependencies: dict = field(default_factory=dict)
    bindings: dict = field(default_factory=dict)
    environments: dict = field(default_factory=dict)
    implementation: object = None
    implementation_names: dict = field(default_factory=dict)
    group_members: tuple = ()

    @property
    def result_count(self):
        return len((self.implementation or self).functions)

    @property
    def stats(self):
        return {"general_lines": len(self.lean.splitlines()),
                "points_lines": len(self.points_lean.splitlines()),
                "facts_lines": len(self.facts_lean.splitlines())}


@dataclass
class ProjectCompilation:
    project: Project
    modules: dict = field(default_factory=dict)
    implementation_modules: dict = field(default_factory=dict)

    @property
    def entry(self):
        return self.modules[self.project.entry]

    @property
    def files(self):
        sources = {}
        for module in (*self.implementation_modules.values(), *self.modules.values()):
            sources[module.lean_module] = module.lean
            sources[module.points_module] = module.points_lean
            if module.facts_lean:
                sources[module.facts_module] = module.facts_lean
        return sources


class _Names(ast.NodeTransformer):
    def __init__(self, owner, names):
        self.owner, self.names = owner, names

    def visit_Import(self, node):
        return None

    def visit_ImportFrom(self, node):
        return None

    def imported(self, node):
        symbol = getattr(node, "_module_symbol", None)
        if symbol is not None and symbol.kind in {"function", "class", "interface"}:
            name = self.names.get(symbol, symbol.name) if symbol.module == self.owner.name else self.names[symbol]
            return ast.copy_location(ast.Name(id=name, ctx=ast.Load()), node)
        return None

    def visit_Name(self, node):
        return self.imported(node) or node

    def visit_Attribute(self, node):
        return self.imported(node) or self.generic_visit(node)

    def visit_Constant(self, node):
        annotation = getattr(node, "_module_annotation", None)
        return self.visit(annotation) if annotation is not None else node


def _tree(owner, names):
    def check_reserved(node):
        spelling = getattr(node, "id", getattr(node, "name", getattr(node, "arg", "")))
        if not isinstance(spelling, str):
            return
        for prefix, purpose in (("_a2l_import_", "import resolution"),
                                ("_a2l_group_", "recursive compilation")):
            if spelling.startswith(prefix):
                raise ProjectError("Names beginning %s are reserved for %s." % (prefix, purpose),
                                   owner.path, getattr(node, "lineno", 1), getattr(node, "col_offset", 0) + 1)

    # Attach provenance before copying: Python AST ids change during deepcopy.
    for node in ast.walk(owner.tree):
        if id(node) in owner.resolved_symbols:
            node._module_symbol = owner.resolved_symbols[id(node)]
        if id(node) in owner.quoted_annotations:
            annotation = owner.quoted_annotations[id(node)]
            for item in ast.walk(annotation):
                check_reserved(item)
                if id(item) in owner.resolved_symbols:
                    item._module_symbol = owner.resolved_symbols[id(item)]
            node._module_annotation = annotation
        check_reserved(node)
    return ast.fix_missing_locations(_Names(owner, names).visit(copy.deepcopy(owner.tree)))


def _imports(project, owner, compiled):
    dependencies = project.transitive_dependencies(owner)
    symbols, names, classes, origins, functions, calls = {}, {}, {}, {}, {}, {}
    execution_indices = {}
    for index, dependency in enumerate(dependencies):
        module = compiled[dependency]
        execution = module.implementation or module
        execution_indices.setdefault(execution.name, index)
        for name, origin in module.class_origins.items():
            if origin.module != dependency:
                continue
            local = "_a2l_import_%d_%s" % (index, origin.name)
            names[origin] = local
            symbols[origin] = (module, name)
        for name in module.functions:
            origin = Symbol(dependency, name, "function")
            # Constructors share their class spelling in source.
            names.setdefault(origin, "_a2l_import_%d_%s" % (index, name))

    def translate(typ, module):
        element = sequence_element(typ)
        if element is not None:
            return sequence_type(translate(element, module))
        base = typ[:-1] if typ.endswith("?") else typ
        if base in module.class_origins:
            base = names[module.class_origins[base]]
        return base + ("?" if typ.endswith("?") else "")

    for origin, (module, name) in symbols.items():
        original = module.classes[name]
        local = names[origin]
        if original.is_interface:
            origins[local] = origin
            continue
        methods = {method: names[Symbol(origin.module, function, "function")]
                   for method, function in original.methods.items()}
        classes[local] = ClassInfo(local, {key: translate(typ, module) for key, typ in original.fields.items()},
                                   methods, local, original.runtime_tag,
                                   module.namespace, origin.name)
        origins[local] = origin
    for index, dependency in enumerate(dependencies):
        module = compiled[dependency]
        for name, original in module.functions.items():
            local = names[Symbol(dependency, name, "function")]
            node = copy.deepcopy(original.node)
            node.name = local
            parameters = [(arg, translate(typ, module)) for arg, typ in original.parameters]
            function = Function(node, parameters, translate(original.return_type, module), dict(parameters),
                                classes=classes,
                                class_name=translate(original.class_name, module) if original.class_name else None,
                                method_name=original.method_name,
                                constructor_for=translate(original.constructor_for, module) if original.constructor_for else None,
                                clocks=set(original.clocks))
            functions[local] = function
            execution = module.implementation or module
            implementation_name = module.implementation_names.get(name, name)
            calls[local] = ImportedCall(function, execution.namespace, implementation_name,
                                        "import_%d" % execution_indices[execution.name],
                                        module.result_count, dependency)
    return names, classes, origins, functions, calls


def _emit(owner, module, declarations):
    from .interfaces import emit_binding, emit_interface
    from .module_parameters import emit_dependency_context
    functions, classes, lowered, imports, clocks = (module.functions, module.classes,
        module.lowered, module.imports, module.clocks)
    imported_modules = {call.frame: call for call in imports.values()}
    lines = ["-- Independently compiled module; imported algorithms keep their own transitions."]
    for declaration in declarations:
        lines.append(emit_interface(declaration))
    if module.dependencies:
        lines += ["structure Dependencies where"]
        for slot in module.dependencies.values():
            lines.append("  «%s» : %s.Code" % (slot.field, slot.namespace))
        lines.append("")
    for name, binding in module.bindings.items():
        lines.append(emit_binding(binding, name=name))
    for name, environment in module.environments.items():
        parameter = " (dependencies : Dependencies)" if module.dependencies else ""
        lines.append("def %s%s : %s.Dependencies where" % (name, parameter, environment.target.namespace))
        lines += ["  «%s» := %s" % item for item in environment.codes.items()]
        lines.append("")
    lines += ["namespace Algo2LeanGenerated", ""]
    emit_classes(lines, classes)
    for slot in module.dependencies.values():
        lines += ["def is_%s (dependencies : Dependencies) (h : Heap) (ref : ObjectRef) : Prop :=" % slot.local_name,
                  "  dependencies.«%s».valid h ref = true" % slot.field, ""]
    emit_collections(lines, collection_types(functions.values()), classes)
    for name, lowerer in lowered.items():
        lines.append("structure State_%s where" % name)
        for field, typ in lowerer.field_types.items():
            lines.append("  %s : %s := %s -- %s" %
                         (field, raw_type(typ), default_value(typ), lowerer.field_labels[field]))
        if not lowerer.field_types:
            lines.append("  unused : Unit := ()")
        lines.append("")
    parameter = " (dependencies : Dependencies)" if module.dependencies else ""
    own_frame = "Frame dependencies" if module.dependencies else "Frame"
    lines += ["inductive Frame%s where" % parameter, "  | invalid"]
    for name in functions:
        lines.append("  | fn_%s (pc : Nat) (state : State_%s)" % (name, name))
    for call in imported_modules.values():
        lines.append("  | %s (frame : %s) (inner : %s) (resume : %s → %s)" %
                     (call.frame, call.source_frame, call.source_stack, call.source_result, own_frame))
    lines += ["", "inductive Result where"]
    for name, function in functions.items():
        lines.append("  | fn_%s (value : %s)" % (name, raw_type(function.return_type)))
    if not functions:
        lines.append("  | unused")
    lines += ["", "abbrev Configuration%s := Algo2LeanCore.Config Heap (%s) Result" % (parameter, own_frame),
              "abbrev Stack%s := Algo2LeanCore.Stack (%s) Result" % (parameter, own_frame),
              "abbrev Transcript%s := List (Configuration%s)" % (parameter, " dependencies" if module.dependencies else ""), ""]
    lines += emit_dependency_context(module, step=False)
    lines += ["inductive Step : Configuration → Configuration → Prop where"]
    for lowerer in lowered.values():
        emit_step(lines, lowerer, lowered, imports)
    for call in imported_modules.values():
        lines += ["  | %s (h : Heap) (frame : %s) (inner : %s)" % (call.frame, call.source_frame, call.source_stack),
                  "      (resume : %s → Frame) (caller : Stack) (after : %s)" % (call.source_result, call.source_config),
                  "      (transition : %s (.active h frame inner) after) :" % call.source_step,
                  "      Step (.active h (Frame.%s frame inner resume) caller)" % call.frame,
                  "        (Algo2LeanCore.ModuleCall.config Frame.%s resume caller after)" % call.frame]
    if module.dependencies:
        lines += ["", 'local notation "Step" => Step dependencies']
    lines += ["", "theorem terminal (h : Heap) (result : Result) :",
              "    Algo2LeanCore.Terminal Step (.done h result) := by",
              "  intro next transition", "  cases transition", ""]
    for call in imported_modules.values():
        lines += ["theorem %s_simulates :" % call.frame,
                  "    Algo2LeanCore.ModuleCall.Simulates Frame.%s %s Step := by" % (call.frame, call.source_step),
                  "  apply Algo2LeanCore.ModuleCall.Delegates.simulates",
                  "  · exact Step.%s" % call.frame,
                  "  · exact %s" % call.source_terminal, ""]
    lines += ["end Algo2LeanGenerated", "", "open Algo2LeanGenerated", ""]
    lines += emit_dependency_context(module)
    for name, lowerer in lowered.items():
        args = input_values(lowerer.function.parameters)
        lines += ["def entry_%s (%s : %s) : Frame :=" %
                  (name, "input" if args else "_input", tuple_type(lowerer.function.parameters)),
                  "  " + frame(lowerer, lowerer.entry, state_value(lowerer, args)), ""]
        if module.dependencies:
            lines += ['local notation "entry_%s" => entry_%s dependencies' % (name, name)]
        emit_public(lines, lowerer, bool(clocks) or bool(module.dependencies),
                    module.namespace, bool(module.dependencies))
    prefix = module.namespace
    header = ["import Algo2LeanLib.Modules"]
    if declarations or module.dependencies or module.bindings:
        header.append("import Algo2LeanLib.Interface")
    header += ["import " + lean_module(dependency) for dependency in owner.dependencies]
    # A named import may re-export a transitive function. Its code is already
    # imported transitively; no duplicate source or namespace is emitted.
    header += ["", "namespace " + prefix, "", "open _root_.Algo2LeanGenerated", ""]
    lean = "\n".join(header + lines + ["end " + prefix, ""])
    points = ["import " + module.lean_module, "", "namespace " + prefix, "",
              "open _root_.Algo2LeanGenerated Algo2LeanGenerated", "",
              "-- Named locations are independent of the compiled module body.", ""]
    points += emit_dependency_context(module)
    for lowerer in lowered.values():
        emit_points(points, lowerer, module.namespace, bool(module.dependencies))
    return credit_generated(lean), credit_generated("\n".join(points + ["end " + prefix, ""]))


def compile_project(entry, *, root=None, sources=None):
    """Compile each .algo dependency once, preserving its public Lean identity."""
    project = entry if isinstance(entry, Project) else load_project(
        entry, root=root if root is not None else Path(entry).resolve().parent, sources=sources)
    result = ProjectCompilation(project)
    from .interfaces import collect_interfaces
    from .module_interfaces import prepare_interfaces, resolve_interfaces
    interfaces = collect_interfaces(project)
    for group in project.compilation_groups:
        if len(group) > 1 or group[0] in project.modules[group[0]].dependencies:
            from .recursive_modules import compile_group
            compile_group(result, group, interfaces)
            continue
        owner = project.modules[group[0]]
        names, classes, origins, external, all_calls = _imports(project, owner, result.modules)
        prepare_interfaces(project, owner, interfaces, names, classes, origins, external, all_calls)
        tree = _tree(owner, names)
        tree.body = [node for node in tree.body if not (isinstance(node, ast.ClassDef) and
                     owner.bindings[node.name].kind == "interface")]
        try:
            # Pure re-export modules have no local declarations.
            if tree.body:
                all_functions, classes = parse_program(tree, imported_functions=external, imported_classes=classes)
                functions = {name: function for name, function in all_functions.items() if name not in external}
            else:
                all_functions, functions = external, {}
            for name, definition in classes.items():
                if name not in origins:
                    origins[name] = Symbol(owner.name, name, "class")
                    definition.runtime_tag = owner.name + "." + name
            if functions:
                assign_points(functions, owner.source)
                validate_generated_names(all_functions)
            clocks = tuple(sorted({clock for function in all_functions.values() for clock in function.clocks}))
            module = CompiledModule(owner.name, namespace(owner.name),
                lean_module(owner.name), "", lean_module(owner.name, "Points"), "",
                functions, classes, origins, {}, {}, clocks)
            resolve_interfaces(owner, module, all_functions, all_calls, result.modules, interfaces)
            module.lowered = {name: Lowerer(function) for name, function in functions.items()}
            module.lean, module.points_lean = _emit(owner, module,
                [info for symbol, info in interfaces.items() if symbol.module == owner.name])
            result.modules[owner.name] = module
            from .module_facts import emit_facts
            module = result.modules[owner.name]
            module.facts_module = lean_module(owner.name, "Facts")
            module.facts_lean = credit_generated(emit_facts(module) + _public_facts(module))
        except CompileError as error:
            if isinstance(error, ProjectError):
                raise
            raise ProjectError(error.message, owner.path, error.line, error.column) from None
        except (RecursionError, MemoryError):
            from .source_validation import RESOURCE_LIMIT
            raise ProjectError(RESOURCE_LIMIT, owner.path) from None
    return result


def _public_facts(module):
    """Emit determinism-based bridges from call summaries to every completed run."""
    from .public_names import function_namespace, function_reference
    lines = ["", "namespace " + module.namespace, "",
             "open Algo2LeanCore _root_.Algo2LeanGenerated Algo2LeanGenerated", ""]
    if module.dependencies:
        from .module_parameters import emit_dependency_context
        lines += emit_dependency_context(module)
        lines += ["variable {dependencies}", ""]
    for name in module.functions:
        public = function_namespace(module.functions[name])
        run = function_reference(module.functions[name], "Run", module.namespace, bool(module.dependencies))
        call = function_reference(module.functions[name], "Call", module.namespace, bool(module.dependencies))
        deterministic = "(deterministic dependencies facts)" if module.dependencies else "deterministic"
        terminal = "terminal dependencies" if module.dependencies else "terminal"
        facts_parameter = " (facts : DependencyFacts dependencies)" if module.dependencies else ""
        lines += ["theorem %s.Run.eq_of_call%s {before after expectedHeap input output expected}" % (public, facts_parameter),
                  "    (run : %s before input after output)" % run,
                  "    (call : %s before input expectedHeap expected) :" % call,
                  "    after = expectedHeap ∧ output = expected := by",
                  "  have same := Reaches.eq_of_terminal (step := Step) %s" % deterministic,
                  "    run.2 call.2.root (%s _ _) (%s _ _)" % (terminal, terminal),
                  "  cases same", "  exact ⟨rfl, rfl⟩", ""]
    return "\n".join(lines + ["end " + module.namespace, ""])
