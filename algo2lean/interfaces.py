"""Method-only interface signatures and checked static implementation bindings.

Interfaces describe executable entries and source types. Their mathematical
behavior and cost laws remain in independent Lean analysis files.
"""

import ast
from dataclasses import dataclass

from .frontend import BUILTINS, NAME_PATTERN, TYPES
from .project import ProjectError, Symbol
from .source_types import sequence_element, sequence_type


@dataclass(frozen=True)
class InterfaceMethod:
    name: str
    # Stored signatures omit the receiver; emission adds the interface reference type.
    parameters: tuple
    return_type: str
    node: ast.FunctionDef


@dataclass
class InterfaceInfo:
    symbol: Symbol
    methods: dict
    node: ast.ClassDef

    @property
    def name(self):
        return self.symbol.name

    @property
    def module(self):
        return self.symbol.module


@dataclass
class InterfaceBinding:
    interface: InterfaceInfo
    backend: object
    class_name: str
    # Method names map to the actual, independently compiled backend functions.
    methods: dict


def _fail(owner, node, message):
    raise ProjectError(message, owner.path, getattr(node, "lineno", 1),
                       getattr(node, "col_offset", 0) + 1)


def _type(project, owner, node, declaration):
    if node is None:
        _fail(owner, declaration, "Interface parameters and results need explicit type annotations.")
    if isinstance(node, ast.Constant):
        if node.value is None:
            return "None"
        if isinstance(node.value, str):
            try:
                parsed = ast.parse(node.value, mode="eval").body
            except (SyntaxError, ValueError):
                _fail(owner, node, "Invalid quoted interface type annotation.")
            for part in ast.walk(parsed):
                ast.copy_location(part, node)
            return _type(project, owner, parsed, declaration)
    if isinstance(node, ast.Name) and node.id in TYPES:
        return node.id
    if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name) and node.value.id == "Seq":
        return sequence_type(_type(project, owner, node.slice, declaration))
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        left = _type(project, owner, node.left, declaration)
        right = _type(project, owner, node.right, declaration)
        if left == "None":
            left, right = right, left
        if right == "None" and left not in TYPES and sequence_element(left) is None and not left.endswith("?"):
            return left + "?"
        _fail(owner, node, "Only class or interface references may be nullable.")
    symbol = project.resolve(owner, node)
    if symbol is not None and symbol.kind in {"class", "interface"}:
        return symbol.canonical_name
    _fail(owner, node, "Unknown or unsupported interface type annotation.")


def collect_interfaces(project):
    """Return local declarations keyed by canonical Symbol, including aliases.

    Imported spellings resolve to the same key. Class types in signatures use
    canonical ``module.Class`` names, so equally named classes stay distinct.
    """
    interfaces = {}
    for owner in project.modules.values():
        for declaration in owner.tree.body:
            if not isinstance(declaration, ast.ClassDef):
                continue
            symbol = owner.bindings.get(declaration.name)
            if symbol is None or symbol.kind != "interface":
                continue
            if declaration.name == "Algo2LeanGenerated":
                _fail(owner, declaration, "Interface name 'Algo2LeanGenerated' is reserved for the generated execution namespace.")
            if declaration.decorator_list or getattr(declaration, "type_params", None):
                _fail(owner, declaration, "Interface decorators and generic type parameters are unsupported.")
            methods = {}
            for member in declaration.body:
                if isinstance(member, ast.Expr) and isinstance(member.value, ast.Constant) and isinstance(member.value.value, str):
                    continue
                if not isinstance(member, ast.FunctionDef):
                    _fail(owner, member, "An interface contains method signatures only; fields and implementations are unsupported.")
                if member.name == "__init__":
                    _fail(owner, member, "Interfaces accept existing objects; constructors are not interface operations.")
                if member.name in methods:
                    _fail(owner, member, "Duplicate interface method '%s'." % member.name)
                if not NAME_PATTERN.fullmatch(member.name):
                    _fail(owner, member, "Interface method names must use ASCII letters, digits, and underscores.")
                if member.name in TYPES or member.name in BUILTINS:
                    _fail(owner, member, "Interface method name '%s' is reserved." % member.name)
                if member.decorator_list or getattr(member, "type_params", None):
                    _fail(owner, member, "Interface methods do not support decorators or generic parameters.")
                arguments = member.args
                if arguments.posonlyargs or arguments.kwonlyargs or arguments.vararg or arguments.kwarg or arguments.defaults or arguments.kw_defaults:
                    _fail(owner, member, "Use plain, explicitly typed positional parameters without defaults.")
                if not arguments.args or arguments.args[0].arg != "self":
                    _fail(owner, member, "An interface method must have self as its first parameter.")
                receiver = arguments.args[0]
                if receiver.annotation is not None and _type(project, owner, receiver.annotation, receiver) != symbol.canonical_name:
                    _fail(owner, receiver, "self must have the declaring interface's type.")
                parameters, seen = [], {"self"}
                for argument in arguments.args[1:]:
                    if not NAME_PATTERN.fullmatch(argument.arg):
                        _fail(owner, argument, "Interface parameter names must use ASCII letters, digits, and underscores.")
                    if argument.arg in seen:
                        _fail(owner, argument, "Duplicate interface parameter '%s'." % argument.arg)
                    if argument.arg in TYPES or argument.arg in BUILTINS:
                        _fail(owner, argument, "Interface parameter name '%s' is reserved." % argument.arg)
                    seen.add(argument.arg)
                    parameters.append((argument.arg, _type(project, owner, argument.annotation, argument)))
                body = list(member.body)
                if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) and isinstance(body[0].value.value, str):
                    body = body[1:]
                if len(body) != 1 or not isinstance(body[0], ast.Expr) or not isinstance(body[0].value, ast.Constant) or body[0].value.value is not Ellipsis:
                    _fail(owner, member, "Interface methods must contain only ... instead of an implementation.")
                methods[member.name] = InterfaceMethod(member.name, tuple(parameters),
                    _type(project, owner, member.returns, member), member)
            if not methods:
                _fail(owner, declaration, "An interface must declare at least one method.")
            interfaces[symbol] = InterfaceInfo(symbol, methods, declaration)
    return interfaces


def canonical_type(typ, class_origins):
    """Resolve a compiled module's local class spellings to canonical types."""
    element = sequence_element(typ)
    if element is not None:
        return sequence_type(canonical_type(element, class_origins))
    nullable = typ.endswith("?")
    base = typ[:-1] if nullable else typ
    if base in class_origins:
        base = class_origins[base].canonical_name
    return base + ("?" if nullable else "")


def _replace_self(typ, interface, concrete):
    element = sequence_element(typ)
    if element is not None:
        return sequence_type(_replace_self(element, interface, concrete))
    nullable = typ.endswith("?")
    base = typ[:-1] if nullable else typ
    return (concrete if base == interface else base) + ("?" if nullable else "")


def check_binding(interface, backend, class_name, *, owner=None, node=None):
    """Check one static implementation; matching signatures prove no laws.

    ``backend`` is an already compiled module. Optional source ``owner`` and
    ``node`` place a diagnostic on the caller's binding expression.
    """
    definition = backend.classes.get(class_name)
    location = node or interface.node
    path = owner.path if owner is not None else interface.module + ".algo"

    def reject(message):
        raise ProjectError(message, path, getattr(location, "lineno", 1),
                           getattr(location, "col_offset", 0) + 1)

    origin = backend.class_origins.get(class_name)
    if definition is None or getattr(definition, "is_interface", False) or (origin and origin.kind == "interface"):
        reject("'%s' is not a concrete implementation class." % class_name)
    concrete = canonical_type(class_name, backend.class_origins)
    methods = {}
    for name, signature in interface.methods.items():
        function_name = definition.methods.get(name)
        if function_name not in backend.functions:
            reject("Class '%s' does not implement interface method '%s'." % (class_name, name))
        function = backend.functions[function_name]
        expected = tuple(_replace_self(typ, interface.symbol.canonical_name, concrete)
                         for _, typ in signature.parameters)
        actual = tuple(canonical_type(typ, backend.class_origins) for _, typ in function.parameters[1:])
        expected_result = _replace_self(signature.return_type, interface.symbol.canonical_name, concrete)
        actual_result = canonical_type(function.return_type, backend.class_origins)
        if actual != expected or actual_result != expected_result:
            reject("Class '%s' has an incompatible signature for interface method '%s'." % (class_name, name))
        methods[name] = function
    return InterfaceBinding(interface, backend, class_name, methods)


def _namespace(module):
    return "Algo." + ".".join("«%s»" % part for part in module.split("."))


def interface_namespace(interface):
    return _namespace(interface.module) + ".«" + interface.name + "»"


def _lean_type(typ):
    """Interface code stores class references in the common identity space.

    Canonical class names are retained by the static signature checker; the
    concrete generated Ref_Class aliases are definitionally ObjectRef too.
    """
    if typ == "Int" or typ == "Bool":
        return typ
    if typ == "None":
        return "Unit"
    if typ == "Seq":
        return "SeqRef"
    if sequence_element(typ) is not None:
        return "CollectionRef"
    return "(Option ObjectRef)" if typ.endswith("?") else "ObjectRef"


def _input_type(method):
    return " × ".join(["ObjectRef"] + [_lean_type(typ) for _, typ in method.parameters])


def _operation(interface, method):
    return interface.name + "_" + method.name


def emit_interface(interface):
    """Emit a declaration inside its owning module's public namespace.

    The owning Generated file imports Algo2LeanLib.Interface and opens the
    runtime Algo2LeanGenerated namespace. No implementation or proof is selected.
    """
    from .public_names import identifier
    lines = ["namespace «" + interface.name + "»", "", "inductive Result where"]
    for method in interface.methods.values():
        lines.append("  | fn_%s (value : %s)" % (_operation(interface, method), _lean_type(method.return_type)))
    lines.extend([
        "", "/-- Executable method entries; behavior and cost laws are separate assumptions. -/",
        "structure Code extends Algo2LeanCore.InterfaceCode Heap Result where",
        "  valid : Heap → ObjectRef → Bool",
    ])
    for method in interface.methods.values():
        lines.append("  entry_%s : %s → Frame" % (_operation(interface, method), _input_type(method)))
    for method in interface.methods.values():
        operation = _operation(interface, method)
        receiver = "input.1" if method.parameters else "input"
        lines.extend([
            "", "/-- The supplied code executes this operation with the stated heap effects. -/",
            "def %s.Call (code : Code) (before : Heap) (input : %s)" % (identifier(method.name), _input_type(method)),
            "    (after : Heap) (output : %s) : Prop :=" % _lean_type(method.return_type),
            "  code.valid before %s = true ∧" % receiver,
            "    Algo2LeanCore.Summary code.Step before (code.entry_%s input) after (.fn_%s output)" %
            (operation, operation),
        ])
    lines.extend(["", "end «" + interface.name + "»", ""])
    return "\n".join(lines)


def _decoder(binding, method, interface_namespace=None):
    original = binding.methods[method.name]
    prefix = interface_namespace or _namespace(binding.interface.module) + ".«" + binding.interface.name + "»"
    source = binding.backend.namespace + ".Algo2LeanGenerated"
    decode = "fun result : %s.Result => match result with | .fn_%s value => some (%s.Result.fn_%s value)" % (
        source, original.name, prefix, _operation(binding.interface, method))
    if len(binding.backend.functions) > 1:
        decode += " | _ => none"
    return "(" + decode + ")"


def emit_binding(binding, *, name, interface_namespace=None):
    """Emit a concrete Code and per-method summary transfers in a caller.

    Binding declarations require only interface and backend Generated imports.
    The backend's optional Facts and mathematical analysis are not imported.
    """
    from .emitter import valid_value
    from .public_names import function_namespace, identifier

    interface = binding.interface
    prefix = interface_namespace or _namespace(interface.module) + ".«" + interface.name + "»"
    backend = binding.backend.namespace
    source = backend + ".Algo2LeanGenerated"
    lines = ["def %s : %s.Code where" % (name, prefix),
             "  toInterfaceCode := Algo2LeanCore.InterfaceAdapter.code %s.Step" % source,
             "  valid := fun heap ref => decide (%s.is_%s heap ref)" % (source, binding.class_name)]
    for method in interface.methods.values():
        original = binding.methods[method.name]
        lines.extend([
            "  entry_%s := fun input =>" % _operation(interface, method),
            "    Algo2LeanCore.InterfaceAdapter.entry (%s.entry_%s input) %s" %
            (backend, original.name, _decoder(binding, method, prefix)),
        ])
    for method in interface.methods.values():
        original = binding.methods[method.name]
        receiver = "input.1" if method.parameters else "input"
        validity_count = sum(valid_value(typ, "argument") is not None for _, typ in original.parameters)
        premise = "contract.1.1" if validity_count > 1 else "contract.1"
        lines.extend([
            "", "theorem %s_summary_%s {before after : Heap} {input : %s} {output : %s}" %
            (name, method.name, _input_type(method), _lean_type(method.return_type)),
            "    (contract : %s.%s.Call before input after output) :" % (backend, function_namespace(original)),
            "    %s.%s.Call %s before input after output := by" % (prefix, identifier(method.name), name),
            "  have receiver_valid : %s.is_%s before %s := %s" % (source, binding.class_name, receiver, premise),
            "  refine ⟨?_, ?_⟩",
            "  · simpa [%s] using receiver_valid" % name,
            "  · exact Algo2LeanCore.InterfaceAdapter.summary %s.terminal contract.2 %s rfl" %
            (source, _decoder(binding, method, prefix)),
        ])
    lines.append("")
    return "\n".join(lines)


def emit_binding_facts(binding, *, name):
    """Emit optional evidence after importing the backend's Facts module."""
    source = binding.backend.namespace + ".Algo2LeanGenerated"
    return ("def %s_facts : Algo2LeanCore.InterfaceFacts %s.toInterfaceCode :=\n"
            "  Algo2LeanCore.InterfaceAdapter.facts %s.next %s.step_next\n" %
            (name, name, source, source))
