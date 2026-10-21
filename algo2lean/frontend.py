"""Static source checking, including fixed-schema mutable Python-style classes.

Class annotations describe the heap schema; they do not initialize objects.
Reading a field before initialization is undefined in the transition semantics.
"""

import ast
import copy
import re
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, Tuple

from .source_types import (is_sequence, make_tuple_type, map_type, parse_type,
                           sequence_element, sequence_type, supports_equality,
                           supports_key, tuple_elements, type_children)
from .real_literals import RealLiteralError, real_literal_ratio


TYPES = {"Int", "Real", "Seq", "Bool", "None"}
TYPE_NAMES = TYPES | {"Tuple", "Set", "Dict"}
NUMERIC_TYPES = {"Int", "Real"}
BUILTINS = {"const", "update", "copy", "range", "tick", "randint", "set", "len", "fork_join"}
NAME_PATTERN = re.compile(r"[A-Za-z_][A-Za-z_0-9]*\Z")


class CompileError(Exception):
    """An input diagnostic, with one-based source coordinates."""

    def __init__(self, message: str, line: int = 1, column: int = 1):
        super().__init__(message)
        self.message = message
        self.line = line
        self.column = column

    def to_dict(self) -> Dict[str, Any]:
        return {"message": self.message, "line": self.line, "column": self.column}


@dataclass
class ClassInfo:
    name: str
    fields: Dict[str, str] = field(default_factory=dict)
    methods: Dict[str, str] = field(default_factory=dict)
    constructor: str = ""
    # Project modules retain canonical class identity through import aliases.
    runtime_tag: Optional[str] = None
    imported_from: Optional[str] = None
    imported_name: Optional[str] = None
    is_interface: bool = False


@dataclass
class Function:
    node: ast.FunctionDef
    parameters: List[Tuple[str, str]]
    return_type: str
    variables: Dict[str, str] = field(default_factory=dict)
    expression_types: Dict[int, str] = field(default_factory=dict)
    assigned_at: Dict[int, Set[str]] = field(default_factory=dict)
    points: Dict[int, Dict[str, Any]] = field(default_factory=dict)
    classes: Dict[str, ClassInfo] = field(default_factory=dict)
    class_name: Optional[str] = None
    method_name: Optional[str] = None
    constructor_for: Optional[str] = None
    clocks: Set[str] = field(default_factory=set)

    @property
    def name(self) -> str:
        return self.node.name


def fail(node: ast.AST, message: str) -> None:
    raise CompileError(message, getattr(node, "lineno", 1), getattr(node, "col_offset", 0) + 1)


def check_name(name: str, node: ast.AST, *, member: bool = False) -> None:
    if not NAME_PATTERN.fullmatch(name):
        fail(node, "Names must use ASCII letters, digits, and underscores.")
    builtins = BUILTINS - {"set", "len"} if member else BUILTINS
    if name in TYPE_NAMES or name in builtins:
        fail(node, "'%s' is reserved." % name)


def annotation(node: Optional[ast.AST], owner: ast.AST,
               classes: Optional[Dict[str, ClassInfo]] = None) -> str:
    """Read annotations without evaluating source text or importing Python code."""
    classes = classes or {}
    if isinstance(node, ast.Constant) and node.value is None:
        return "None"
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        try:
            parsed = ast.parse(node.value, mode="eval").body
        except (SyntaxError, ValueError):
            fail(node, "Invalid quoted type annotation.")
        # Keep diagnostics on the source annotation, not inside the quoted text.
        for part in ast.walk(parsed):
            ast.copy_location(part, node)
        return annotation(parsed, owner, classes)
    if isinstance(node, ast.Name) and (node.id in TYPES or node.id in classes):
        return node.id
    if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name) and node.value.id == "Seq":
        return sequence_type(annotation(node.slice, owner, classes))
    if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name) and node.value.id == "Tuple":
        elements = node.slice.elts if isinstance(node.slice, ast.Tuple) else [node.slice]
        return make_tuple_type(annotation(element, owner, classes) for element in elements)
    if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name) and node.value.id in {"Set", "Dict"}:
        elements = node.slice.elts if isinstance(node.slice, ast.Tuple) else [node.slice]
        arity = 1 if node.value.id == "Set" else 2
        if len(elements) != arity:
            fail(node, "%s expects %d type argument(s)." % (node.value.id, arity))
        types = [annotation(element, owner, classes) for element in elements]
        require_key_type(elements[0], types[0], lambda name: name in classes and classes[name].is_interface)
        return "%s[%s]" % (node.value.id, ", ".join(types))
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        left = annotation(node.left, owner, classes)
        right = annotation(node.right, owner, classes)
        if left == "None" and right in classes:
            return right + "?"
        if right == "None" and left in classes:
            return left + "?"
        fail(node, "Only nullable class references, written ClassName | None, are supported as unions.")
    fail(node or owner, "A type annotation must be Int, Real, Bool, None, Seq, Seq[ElementType], Tuple[ElementTypes], Set[KeyType], Dict[KeyType, ValueType], a class name, or ClassName | None.")


def reference_class(typ: str, classes: Dict[str, ClassInfo]) -> Optional[str]:
    base = typ[:-1] if typ.endswith("?") else typ
    return base if base in classes else None


def require_key_type(node, typ, is_interface=lambda name: False):
    """Finite keys compare immutable values or concrete object identities."""
    if not supports_key(typ, allow_real=True):
        fail(node, "Set elements and dictionary keys must be Int, Real, Bool, None, concrete object references, or tuples of these types.")
    def visit(tree):
        if is_interface(tree.name):
            fail(node, "Abstract interface references cannot be set elements or dictionary keys.")
        for child in tree.arguments:
            visit(child)
    visit(parse_type(typ))


def finite_kind(typ):
    kind = parse_type(typ).name
    return kind if kind in {"Set", "Dict"} else None


class Checker:
    def __init__(self, functions: Dict[str, Function], function: Function):
        self.functions = functions
        self.function = function
        self.classes = function.classes

    def expect(self, node: ast.AST, actual: str, expected: str, *, record: bool = True) -> None:
        if actual == expected:
            return
        if actual == "Int" and expected == "Real":
            if record:
                node.expected_type = expected
            return
        if record and isinstance(node, (ast.Set, ast.Dict)) and finite_kind(actual) == finite_kind(expected):
            # A new literal may adopt contextual element/value types. An alias
            # cannot: assigning wider types through it would break other views.
            expected_parts = type_children(expected)
            if isinstance(node, ast.Set):
                for element in node.elts:
                    self.expect(element, self.function.expression_types[id(element)], expected_parts[0])
            else:
                for key, value in zip(node.keys, node.values):
                    self.expect(key, self.function.expression_types[id(key)], expected_parts[0])
                    self.expect(value, self.function.expression_types[id(value)], expected_parts[1])
            self.function.expression_types[id(node)] = expected
            return
        actual_tuple, expected_tuple = tuple_elements(actual), tuple_elements(expected)
        if actual_tuple is not None and expected_tuple is not None:
            if len(actual_tuple) != len(expected_tuple):
                fail(node, "Expected %s, got %s (different tuple arities)." % (expected, actual))
            if record and isinstance(node, ast.Tuple):
                for element, found, wanted in zip(node.elts, actual_tuple, expected_tuple):
                    self.expect(element, found, wanted)
                # Literal components now produce their contextual types. The
                # lowerer must not wrap their nullable coercions a second time.
                self.function.expression_types[id(node)] = expected
            else:
                for found, wanted in zip(actual_tuple, expected_tuple):
                    self.expect(node, found, wanted, record=False)
                if record:
                    node.expected_type = expected
            return
        if (expected in self.classes and self.classes[expected].is_interface
                and actual in self.classes and not self.classes[actual].is_interface):
            # Structural method compatibility selects executable code only.
            # Behavioral laws are proved separately in Lean.
            for method, required in self.classes[expected].methods.items():
                supplied = self.classes[actual].methods.get(method)
                if supplied is None:
                    fail(node, "Class '%s' does not implement interface method '%s'." % (actual, method))
                wanted, found = self.functions[required], self.functions[supplied]
                def concrete(typ):
                    return map_type(typ, lambda name: actual if name == expected else name)
                if ([concrete(typ) for _, typ in wanted.parameters[1:]] !=
                        [typ for _, typ in found.parameters[1:]] or
                        concrete(wanted.return_type) != found.return_type):
                    fail(node, "Class '%s' has an incompatible signature for interface method '%s'." % (actual, method))
            if record:
                node.expected_type = expected
            return
        if expected.endswith("?") and actual in (expected[:-1], "None"):
            if record:
                node.expected_type = expected
            return
        # A fresh allocation may choose the contextual element type.  Existing
        # mutable sequences are invariant: widening an alias would let a None
        # write invalidate a reference held elsewhere as Seq[ClassName].
        actual_element = sequence_element(actual)
        expected_element = sequence_element(expected)
        if (record and actual_element is not None and expected_element is not None
                and isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id == "const" and len(node.args) == 1):
            self.expect(node.args[0], actual_element, expected_element)
            self.function.expression_types[id(node)] = expected
            return
        fail(node, "Expected %s, got %s." % (expected, actual))

    def common_value_type(self, left: str, right: str) -> Optional[str]:
        """Join numeric values, immutable tuple components, and nullable references."""
        if left == right:
            return left
        if left in NUMERIC_TYPES and right in NUMERIC_TYPES:
            return "Real"
        left_tuple, right_tuple = tuple_elements(left), tuple_elements(right)
        if left_tuple is not None and right_tuple is not None and len(left_tuple) == len(right_tuple):
            components = [self.common_value_type(first, second)
                          for first, second in zip(left_tuple, right_tuple)]
            if all(component is not None for component in components):
                return make_tuple_type(components)
            return None
        left_class, right_class = reference_class(left, self.classes), reference_class(right, self.classes)
        if (left_class and (right_class == left_class or right == "None")) or (right_class and left == "None"):
            return (left_class or right_class) + "?"
        return None

    def tuple_comparison(self, node: ast.Compare, operands, types) -> None:
        """Give a comparison chain one common type so its middle value is shared."""
        if any(isinstance(op, (ast.Is, ast.IsNot)) for op in node.ops):
            fail(node, "Tuples are immutable values; is and is not do not compare tuple identity.")
        if any(not isinstance(op, (ast.Eq, ast.NotEq)) for op in node.ops):
            fail(node, "Tuple comparisons support == and != only; tuple ordering is not supported.")
        common = types[0]
        for typ in types[1:]:
            common = self.common_value_type(common, typ)
            if common is None:
                fail(node, "Tuple equality requires matching component types and arities.")
        if not supports_equality(common):
            fail(node, "Tuple equality requires equality for every component; mutable collections cannot be compared.")
        for operand, typ in zip(operands, types):
            self.expect(operand, typ, common)

    def sequence(self, node: ast.AST, assigned: Set[str]) -> Tuple[str, str]:
        typ = self.expr(node, assigned)
        element = sequence_element(typ)
        if element is None:
            fail(node, "Expected a sequence, got %s." % typ)
        return typ, element

    def bind(self, node: ast.Name, typ: str, assigned: Set[str]) -> Set[str]:
        check_name(node.id, node)
        if node.id in self.functions:
            fail(node, "A local variable cannot shadow function '%s'." % node.id)
        previous = self.function.variables.get(node.id)
        if previous is not None:
            self.expect(node, typ, previous)
            typ = previous
        self.function.variables[node.id] = typ
        self.function.expression_types[id(node)] = typ
        return assigned | {node.id}

    def expr(self, node: ast.AST, assigned: Set[str], expected: Optional[str] = None) -> str:
        typ = self._expr(node, assigned, expected)
        self.function.expression_types[id(node)] = typ
        if expected is not None:
            self.expect(node, typ, expected)
            return getattr(node, "expected_type", self.function.expression_types[id(node)])
        return typ

    def literal_type(self, owner, elements, assigned, expected=None):
        """Infer homogeneous literal contents, then apply one immutable join."""
        if not elements:
            if expected is None:
                fail(owner, "An empty collection needs an expected type, such as Set[Int] or Dict[Int, Int].")
            return expected
        types = [self.expr(element, assigned, expected) for element in elements]
        common = expected or types[0]
        for typ in types[1:]:
            joined = self.common_value_type(common, typ)
            if joined is None:
                fail(owner, "Collection literal entries must have compatible types; got %s and %s." % (common, typ))
            common = joined
        for element, typ in zip(elements, types):
            self.expect(element, typ, common)
        return common

    def collection_literal(self, node, assigned, expected):
        kind = "Set" if isinstance(node, ast.Set) else "Dict"
        context = type_children(expected) if expected is not None and finite_kind(expected) == kind else ()
        if kind == "Set":
            if any(isinstance(element, ast.Starred) for element in node.elts):
                fail(node, "Starred set expansion is not supported.")
            key = self.literal_type(node, node.elts, assigned, context[0] if context else None)
            value = None
        else:
            if any(key is None for key in node.keys):
                fail(node, "Expanded dictionary entries are not supported.")
            # Typecheck each key/value pair in source order as the lowerer will
            # evaluate it; contextual empty values acquire their declared type.
            key_types, value_types = [], []
            for key_node, value_node in zip(node.keys, node.values):
                key_types.append(self.expr(key_node, assigned, context[0] if context else None))
                value_types.append(self.expr(value_node, assigned, context[1] if context else None))
            def joined(nodes, types, wanted):
                if not types:
                    if wanted is None:
                        fail(node, "An empty dictionary needs an expected Dict[KeyType, ValueType].")
                    return wanted
                common = wanted or types[0]
                for typ in types[1:]:
                    merged = self.common_value_type(common, typ)
                    if merged is None:
                        fail(node, "Dictionary literal entries must have compatible types; got %s and %s." % (common, typ))
                    common = merged
                for entry, typ in zip(nodes, types):
                    self.expect(entry, typ, common)
                return common
            key = joined(node.keys, key_types, context[0] if context else None)
            value = joined(node.values, value_types, context[1] if context else None)
        require_key_type(node, key, lambda name: name in self.classes and self.classes[name].is_interface)
        return "Set[%s]" % key if kind == "Set" else "Dict[%s, %s]" % (key, value)

    def attribute(self, node: ast.Attribute, assigned: Set[str]) -> str:
        receiver = self.expr(node.value, assigned)
        name = reference_class(receiver, self.classes)
        if name is None:
            fail(node, "Field access requires a class reference, got %s." % receiver)
        fields = self.classes[name].fields
        if node.attr not in fields:
            fail(node, "Class '%s' has no declared field '%s'." % (name, node.attr))
        node.class_name = name
        self.function.expression_types[id(node)] = fields[node.attr]
        return fields[node.attr]

    def comparable(self, node: ast.AST, left: str, right: str, identity: bool) -> None:
        if finite_kind(left) or finite_kind(right):
            fail(node, "Set and dictionary equality and identity comparisons are not supported; use membership or lookup.")
        if is_sequence(left) or is_sequence(right):
            fail(node, "Sequence equality is not a decidable condition; compare elements instead.")
        left_class = reference_class(left, self.classes)
        right_class = reference_class(right, self.classes)
        if left_class or right_class or left == "None" or right == "None":
            if left == right or (left_class and left_class == right_class) or (
                    left_class and right == "None") or (right_class and left == "None"):
                return
            fail(node, "Cannot compare references of different classes or references with primitive values.")
        if identity:
            fail(node, "is and is not compare class references and None only.")
        self.expect(node, right, left)

    def _expr(self, node: ast.AST, assigned: Set[str], context: Optional[str] = None) -> str:
        if isinstance(node, ast.Constant):
            if node.value is None:
                return "None"
            if type(node.value) is bool:
                return "Bool"
            if type(node.value) is int:
                return "Int"
            if type(node.value) is float:
                try:
                    real_literal_ratio(node)
                except RealLiteralError as error:
                    fail(node, str(error))
                return "Real"
            fail(node, "Only integer, real, Boolean, and None literals are supported.")
        if isinstance(node, ast.Name):
            if node.id not in assigned:
                fail(node, "Variable '%s' may be unassigned here." % node.id)
            return self.function.variables[node.id]
        if isinstance(node, ast.Tuple):
            if any(isinstance(element, ast.Starred) for element in node.elts):
                fail(node, "Starred tuple expansion is not supported.")
            expected = tuple_elements(context) if context is not None else None
            if expected is not None and len(expected) != len(node.elts):
                fail(node, "Expected %s, got a tuple with %d component(s)." % (context, len(node.elts)))
            return make_tuple_type(self.expr(element, assigned, expected[index] if expected is not None else None)
                                   for index, element in enumerate(node.elts))
        if isinstance(node, (ast.Set, ast.Dict)):
            return self.collection_literal(node, assigned, context)
        if isinstance(node, ast.Attribute):
            return self.attribute(node, assigned)
        if isinstance(node, ast.UnaryOp):
            if isinstance(node.op, ast.Not):
                self.expect(node.operand, self.expr(node.operand, assigned), "Bool")
                return "Bool"
            if isinstance(node.op, (ast.UAdd, ast.USub)):
                typ = self.expr(node.operand, assigned)
                if typ not in NUMERIC_TYPES:
                    fail(node.operand, "Unary + and - require Int or Real, got %s." % typ)
                return typ
            fail(node, "Unsupported unary operator.")
        if isinstance(node, ast.BinOp):
            if not isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.Div, ast.FloorDiv, ast.Mod)):
                fail(node, "Supported arithmetic operators are +, -, *, /, //, and %.")
            left = self.expr(node.left, assigned)
            right = self.expr(node.right, assigned)
            if isinstance(node.op, (ast.FloorDiv, ast.Mod)):
                self.expect(node.left, left, "Int")
                self.expect(node.right, right, "Int")
                return "Int"
            for operand, typ in ((node.left, left), (node.right, right)):
                if typ not in NUMERIC_TYPES:
                    fail(operand, "Arithmetic requires Int or Real, got %s." % typ)
            result = "Real" if isinstance(node.op, ast.Div) or "Real" in (left, right) else "Int"
            self.expect(node.left, left, result)
            self.expect(node.right, right, result)
            return result
        if isinstance(node, ast.BoolOp):
            for value in node.values:
                self.expect(value, self.expr(value, assigned), "Bool")
            return "Bool"
        if isinstance(node, ast.Compare):
            operands = [node.left] + node.comparators
            types = [self.expr(operand, assigned) for operand in operands]
            if any(isinstance(op, (ast.In, ast.NotIn)) for op in node.ops):
                if len(node.ops) != 1:
                    fail(node, "Chained membership comparisons are not supported; combine separate comparisons with and.")
                kind = finite_kind(types[1])
                if kind is None:
                    fail(node.comparators[0], "Membership requires a finite set or dictionary.")
                self.expect(node.left, types[0], type_children(types[1])[0])
                return "Bool"
            if any(tuple_elements(typ) is not None for typ in types):
                self.tuple_comparison(node, operands, types)
                return "Bool"
            if all(typ in NUMERIC_TYPES for typ in types):
                if any(isinstance(op, (ast.Is, ast.IsNot)) for op in node.ops):
                    fail(node, "is and is not compare class references and None only.")
                common = "Real" if "Real" in types else "Int"
                for operand, typ in zip(operands, types):
                    self.expect(operand, typ, common)
                return "Bool"
            left_type = types[0]
            for op, right, right_type in zip(node.ops, node.comparators, types[1:]):
                if isinstance(op, (ast.Eq, ast.NotEq, ast.Is, ast.IsNot)):
                    self.comparable(right, left_type, right_type, isinstance(op, (ast.Is, ast.IsNot)))
                elif isinstance(op, (ast.Lt, ast.LtE, ast.Gt, ast.GtE)):
                    self.expect(node, left_type, "Int")
                    self.expect(right, right_type, "Int")
                else:
                    fail(node, "Supported comparisons are ==, !=, is, is not, <, <=, >, and >=.")
                left_type = right_type
            return "Bool"
        if isinstance(node, ast.IfExp):
            self.expect(node.test, self.expr(node.test, assigned), "Bool")
            yes = self.expr(node.body, assigned, context)
            no = self.expr(node.orelse, assigned, context)
            if yes == no:
                return yes
            result = self.common_value_type(yes, no)
            if result is not None:
                self.expect(node.body, yes, result)
                self.expect(node.orelse, no, result)
                return result
            self.expect(node.orelse, no, yes)
            return yes
        if isinstance(node, ast.Subscript):
            typ = self.expr(node.value, assigned)
            if finite_kind(typ) == "Dict":
                key, value = type_children(typ)
                self.expr(node.slice, assigned, key)
                return value
            if finite_kind(typ) == "Set":
                fail(node, "Sets do not support indexing; use membership with in.")
            elements = tuple_elements(typ)
            if elements is not None:
                index = node.slice
                sign = 1
                if isinstance(index, ast.UnaryOp) and isinstance(index.op, (ast.USub, ast.UAdd)):
                    sign = -1 if isinstance(index.op, ast.USub) else 1
                    index = index.operand
                if not isinstance(index, ast.Constant) or type(index.value) is not int:
                    fail(node.slice, "Tuple indexing requires an integer literal; dynamic indices and slices are not supported.")
                index = sign * index.value
                normalized = index + len(elements) if index < 0 else index
                if not 0 <= normalized < len(elements):
                    fail(node.slice, "Tuple index %d is out of range for %d component(s)." % (index, len(elements)))
                node.tuple_index = normalized
                self.function.expression_types[id(node.slice)] = "Int"
                return elements[normalized]
            element = sequence_element(typ)
            if element is None:
                fail(node.value, "Expected a sequence or tuple, got %s." % typ)
            self.expect(node.slice, self.expr(node.slice, assigned), "Int")
            return element
        if isinstance(node, ast.Call):
            if getattr(node, "allocate_class", None):
                return node.allocate_class
            if node.keywords:
                fail(node, "Keyword and expanded arguments are not supported.")
            args = node.args
            if isinstance(node.func, ast.Attribute):
                receiver_type = self.expr(node.func.value, assigned)
                kind = finite_kind(receiver_type)
                if kind is not None:
                    parts = type_children(receiver_type)
                    if kind == "Set" and node.func.attr in {"add", "discard"}:
                        expected = [parts[0]]
                        result = "None"
                        operation = "set_" + node.func.attr
                    elif kind == "Dict" and node.func.attr == "get":
                        expected = [parts[0], parts[1]]
                        result = parts[1]
                        operation = "dict_get"
                    else:
                        fail(node.func, "Unsupported %s method '%s'." % (kind, node.func.attr))
                    if len(args) != len(expected):
                        fail(node, "'%s' expects %d argument(s), got %d." % (node.func.attr, len(expected), len(args)))
                    node.receiver = node.func.value
                    node.collection_operation = operation
                    for argument, typ in zip(args, expected):
                        self.expr(argument, assigned, typ)
                    return result
                class_name = reference_class(receiver_type, self.classes)
                if class_name is None:
                    fail(node.func, "Method calls require a class reference.")
                methods = self.classes[class_name].methods
                if node.func.attr not in methods:
                    fail(node.func, "Class '%s' has no method '%s'." % (class_name, node.func.attr))
                name = methods[node.func.attr]
                node.receiver = node.func.value
                node.resolved_name = name
                # Nullable receivers are checked dynamically at the call boundary.
                function = self.functions[name]
                expected = [typ for _, typ in function.parameters[1:]]
                result = function.return_type
            elif isinstance(node.func, ast.Name):
                name = node.func.id
                if name == "fork_join":
                    if len(args) != 2:
                        fail(node, "fork_join expects exactly two direct function calls.")
                    results = []
                    for child in args:
                        if not (isinstance(child, ast.Call) and isinstance(child.func, ast.Name)
                                and child.func.id in self.functions):
                            fail(child, "Each fork_join branch must be a direct Algo2Lean function call.")
                        results.append(self.expr(child, assigned))
                    node.fork_join = True
                    return make_tuple_type(results)
                elif name == "Real":
                    if len(args) != 1:
                        fail(node, "Real expects one Int or Real argument.")
                    self.expr(args[0], assigned, "Real")
                    node.real_conversion = True
                    return "Real"
                elif name in ("const", "update", "copy"):
                    count = 3 if name == "update" else 1
                    if len(args) != count:
                        fail(node, "'%s' expects %d argument(s), got %d." % (name, count, len(args)))
                    if name == "const":
                        expected_element = sequence_element(context) if context is not None else None
                        return sequence_type(self.expr(args[0], assigned, expected_element))
                    if name == "copy":
                        source = self.expr(args[0], assigned, context if context and finite_kind(context) else None)
                        if finite_kind(source):
                            node.collection_operation = "copy"
                            return source
                        element = sequence_element(source)
                        if element is None:
                            fail(args[0], "Expected a sequence, set, or dictionary for copy, got %s." % source)
                        return source
                    result, element = self.sequence(args[0], assigned)
                    if name == "update":
                        self.expect(args[1], self.expr(args[1], assigned), "Int")
                        self.expr(args[2], assigned, element)
                    return result
                elif name == "set":
                    if args:
                        fail(node, "set() takes no arguments; use a set literal for initial elements.")
                    if context is None or finite_kind(context) != "Set":
                        fail(node, "An empty set needs an expected Set[ElementType].")
                    return context
                elif name == "len":
                    if len(args) != 1:
                        fail(node, "len expects one finite set or dictionary.")
                    source = self.expr(args[0], assigned)
                    if not finite_kind(source):
                        fail(args[0], "len requires a finite set or dictionary; sequences have every integer index.")
                    node.collection_operation = "length"
                    return "Int"
                elif name == "randint":
                    expected = ["Int", "Int"]
                    result = "Int"
                elif name == "range":
                    fail(node, "range is supported only in a for statement.")
                elif name == "tick":
                    fail(node, 'tick("clock_name", amount) is supported only as a standalone statement.')
                elif name in self.functions:
                    function = self.functions[name]
                    if function.class_name and not getattr(node, "synthetic", False):
                        fail(node, "Call method '%s' through an object." % function.method_name)
                    expected = [typ for _, typ in function.parameters]
                    result = function.return_type
                    node.resolved_name = name
                else:
                    fail(node, "Unknown function '%s'." % name)
            else:
                fail(node, "Only calls to named Algo2Lean functions or object methods are supported.")
            if len(args) != len(expected):
                fail(node, "'%s' expects %d argument(s), got %d." % (name, len(expected), len(args)))
            for arg, typ in zip(args, expected):
                self.expr(arg, assigned, typ)
            return result
        fail(node, "Unsupported expression: %s." % type(node).__name__)

    def block(self, statements: List[ast.stmt], assigned: Set[str]) -> Optional[Set[str]]:
        current = set(assigned)
        live = True
        for statement in statements:
            result = self.statement(statement, current)
            if result is not None:
                current = result
            else:
                live = False
        return current if live else None

    def assign_target(self, target: ast.AST, value: ast.AST, typ: str,
                      assigned: Set[str]) -> Set[str]:
        if isinstance(target, ast.Tuple):
            return self.unpack_target(target, typ, assigned)
        if isinstance(target, ast.Name):
            expected = self.function.variables.get(target.id, typ)
            self.expect(value, typ, expected)
            return self.bind(target, expected, assigned)
        if isinstance(target, ast.Attribute):
            self.expect(value, typ, self.attribute(target, assigned))
            return assigned
        if isinstance(target, ast.Subscript):
            container = self.expr(target.value, assigned)
            if finite_kind(container) == "Dict":
                key, element = type_children(container)
                self.expr(target.slice, assigned, key)
                self.expect(value, typ, element)
                self.function.expression_types[id(target)] = element
                return assigned
            if finite_kind(container) == "Set":
                fail(target, "Sets do not support indexed assignment; use add or discard.")
            if tuple_elements(container) is not None:
                fail(target, "Tuple components cannot be assigned; create a new tuple instead.")
            element = sequence_element(container)
            if element is None:
                fail(target.value, "Expected a sequence, got %s." % container)
            self.expect(target.slice, self.expr(target.slice, assigned), "Int")
            self.expect(value, typ, element)
            self.function.expression_types[id(target)] = element
            return assigned
        fail(target, "Assignment target must be a variable, tuple of variables, declared object field, sequence element, or dictionary entry.")

    def assignment_context(self, target, assigned):
        """Find a known destination type without evaluating or rewriting the RHS."""
        if isinstance(target, ast.Name):
            return self.function.variables.get(target.id)
        if isinstance(target, ast.Attribute):
            return self.attribute(target, assigned)
        if isinstance(target, ast.Subscript):
            container = self.expr(target.value, assigned)
            if finite_kind(container) == "Dict":
                return type_children(container)[1]
            return sequence_element(container)
        if isinstance(target, ast.Tuple):
            components = [self.assignment_context(child, assigned) if isinstance(child, (ast.Tuple, ast.Name))
                          else None for child in target.elts]
            if all(component is not None for component in components):
                return make_tuple_type(components)
        return None

    def unpack_target(self, target: ast.AST, actual: str, assigned: Set[str]) -> Set[str]:
        """Record destination types while leaving the single RHS expression intact."""
        if isinstance(target, ast.Name):
            expected = self.function.variables.get(target.id, actual)
            self.expect(target, actual, expected)
            return self.bind(target, expected, assigned)
        if isinstance(target, ast.Starred):
            fail(target, "Starred tuple unpacking is not supported.")
        if not isinstance(target, ast.Tuple):
            fail(target, "Tuple unpacking targets must be variables or nested tuples of variables.")
        if any(isinstance(component, ast.Starred) for component in target.elts):
            fail(target, "Starred tuple unpacking is not supported.")
        elements = tuple_elements(actual)
        if elements is None:
            fail(target, "Tuple unpacking requires a tuple value, got %s." % actual)
        if len(target.elts) != len(elements):
            fail(target, "Tuple unpacking has %d target(s), but the value has %d component(s)." % (len(target.elts), len(elements)))
        for component, typ in zip(target.elts, elements):
            assigned = self.unpack_target(component, typ, assigned)
        self.function.expression_types[id(target)] = make_tuple_type(
            self.function.expression_types[id(component)] for component in target.elts)
        return assigned

    def statement(self, node: ast.stmt, assigned: Set[str]) -> Optional[Set[str]]:
        if not getattr(node, "synthetic", False):
            self.function.assigned_at[id(node)] = set(assigned)
        if isinstance(node, ast.Return):
            if node.value is None:
                if self.function.return_type != "None":
                    fail(node, "Return must supply a value.")
                node.value = ast.copy_location(ast.Constant(value=None), node)
            self.expr(node.value, assigned, self.function.return_type)
            return None
        if isinstance(node, ast.Pass):
            return assigned
        if isinstance(node, ast.Assign):
            if len(node.targets) != 1:
                fail(node, "Use a separate assignment for each variable.")
            context = self.assignment_context(node.targets[0], assigned)
            typ = self.expr(node.value, assigned, context)
            return self.assign_target(node.targets[0], node.value, typ, assigned)
        if isinstance(node, ast.AnnAssign):
            typ = annotation(node.annotation, node, self.classes)
            if node.value is None:
                fail(node, "A local declaration must include an initial value.")
            self.expr(node.value, assigned, typ)
            if isinstance(node.target, ast.Name):
                return self.bind(node.target, typ, assigned)
            if isinstance(node.target, ast.Attribute) and self.function.method_name == "__init__" and (
                    isinstance(node.target.value, ast.Name) and node.target.value.id == "self"):
                expected = self.attribute(node.target, assigned)
                if typ != expected:
                    fail(node, "Field annotation must match the declared field type %s." % expected)
                return assigned
            fail(node, "Annotated assignment requires a variable or a self.field declaration in __init__.")
        if isinstance(node, ast.Delete):
            if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Subscript):
                fail(node, "Deletion supports a single dictionary entry: del dictionary[key].")
            target = node.targets[0]
            container = self.expr(target.value, assigned)
            if finite_kind(container) != "Dict":
                fail(target, "Deletion supports dictionary entries only.")
            key, value = type_children(container)
            self.expr(target.slice, assigned, key)
            self.function.expression_types[id(target)] = value
            return assigned
        if isinstance(node, ast.AugAssign):
            if isinstance(node.target, ast.Subscript):
                container = self.expr(node.target.value, assigned)
                if tuple_elements(container) is not None:
                    fail(node.target, "Tuple components cannot be assigned; create a new tuple instead.")
            if not isinstance(node.target, (ast.Name, ast.Attribute)):
                fail(node, "Augmented assignment requires an Int or Real variable or field.")
            if not isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.Div, ast.FloorDiv, ast.Mod)):
                fail(node, "Unsupported augmented assignment operator.")
            target = self.expr(node.target, assigned)
            if target not in NUMERIC_TYPES:
                fail(node.target, "Augmented assignment requires Int or Real, got %s." % target)
            if isinstance(node.op, (ast.FloorDiv, ast.Mod)):
                self.expect(node.target, target, "Int")
            if isinstance(node.op, ast.Div) and target != "Real":
                fail(node.target, "The /= operator requires a Real target; an Int variable or field keeps its type.")
            self.expr(node.value, assigned, target)
            return assigned
        if isinstance(node, ast.If):
            self.expect(node.test, self.expr(node.test, assigned), "Bool")
            yes = self.block(node.body, assigned)
            no = self.block(node.orelse, assigned)
            if yes is None:
                return no
            if no is None:
                return yes
            return yes & no
        if isinstance(node, ast.While):
            if node.orelse:
                fail(node, "while ... else is not supported.")
            self.expect(node.test, self.expr(node.test, assigned), "Bool")
            self.block(node.body, assigned)
            if isinstance(node.test, ast.Constant) and node.test.value is True:
                return None
            return assigned
        if isinstance(node, ast.For):
            if node.orelse:
                fail(node, "for ... else is not supported.")
            if not isinstance(node.target, ast.Name):
                fail(node, "A for loop requires a simple variable; unpacking loop targets is not supported.")
            iterator = node.iter
            if not isinstance(iterator, ast.Call) or not isinstance(iterator.func, ast.Name) or iterator.func.id != "range":
                typ = self.expr(iterator, assigned)
                if finite_kind(typ) is None:
                    fail(node.iter, "A for loop must iterate over range(...), a finite set, or a dictionary.")
                node.collection_iteration = typ
                body_assigned = self.bind(node.target, type_children(typ)[0], assigned)
                self.block(node.body, body_assigned)
                return assigned
            if iterator.keywords or not 1 <= len(iterator.args) <= 3:
                fail(iterator, "range takes one, two, or three positional integer arguments.")
            for argument in iterator.args:
                self.expect(argument, self.expr(argument, assigned), "Int")
            body_assigned = self.bind(node.target, "Int", assigned)
            self.block(node.body, body_assigned)
            return assigned
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
            call = node.value
            if isinstance(call.func, ast.Name) and call.func.id == "tick":
                if call.keywords or not 1 <= len(call.args) <= 2:
                    fail(call, 'Use tick("clock_name") or tick("clock_name", amount) with positional arguments.')
                name = call.args[0]
                if not (isinstance(name, ast.Constant) and isinstance(name.value, str)
                        and NAME_PATTERN.fullmatch(name.value)):
                    fail(name, "A clock name must be a string literal containing an ASCII identifier.")
                node.clock_name = name.value
                node.tick_amount = call.args[1] if len(call.args) == 2 else None
                if node.tick_amount is not None:
                    self.expect(node.tick_amount, self.expr(node.tick_amount, assigned), "Int")
                self.function.clocks.add(name.value)
                return assigned
            self.expr(node.value, assigned)
            return assigned
        fail(node, "Unsupported statement: %s." % type(node).__name__)


def _function(node: ast.FunctionDef, classes: Dict[str, ClassInfo],
              class_name: Optional[str] = None) -> Function:
    check_name(node.name, node, member=class_name is not None)
    if node.decorator_list or getattr(node, "type_params", None):
        fail(node, "Decorators and generic type parameters are not supported.")
    arguments = node.args
    if arguments.posonlyargs or arguments.kwonlyargs or arguments.vararg or arguments.kwarg or arguments.defaults or arguments.kw_defaults:
        fail(node, "Use plain, explicitly typed positional parameters without defaults.")
    if class_name and (not arguments.args or arguments.args[0].arg != "self"):
        fail(node, "An instance method must have self as its first parameter.")
    parameters = []
    seen = set()
    for index, parameter in enumerate(arguments.args):
        check_name(parameter.arg, parameter)
        if parameter.arg in seen:
            fail(parameter, "Duplicate parameter '%s'." % parameter.arg)
        seen.add(parameter.arg)
        if class_name and index == 0:
            typ = class_name if parameter.annotation is None else annotation(parameter.annotation, parameter, classes)
            if typ != class_name:
                fail(parameter, "self must have type %s." % class_name)
        else:
            typ = annotation(parameter.annotation, parameter, classes)
        parameters.append((parameter.arg, typ))
    result = annotation(node.returns, node, classes)
    method_name = node.name if class_name else None
    if class_name:
        if node.name == "__init__" and result != "None":
            fail(node, "__init__ must return None.")
        node.name = class_name + "_" + node.name
    return Function(node, parameters, result, dict(parameters), classes=classes,
                    class_name=class_name, method_name=method_name)


def _synthetic(node: ast.AST, source: ast.AST) -> ast.AST:
    for part in ast.walk(node):
        ast.copy_location(part, source)
        part.synthetic = True
    return ast.fix_missing_locations(node)


def _constructor(info: ClassInfo, source: ast.ClassDef, initializer: Optional[Function],
                 classes: Dict[str, ClassInfo], function_names: Set[str]) -> Function:
    parameters = initializer.parameters[1:] if initializer else []
    arguments = copy.deepcopy(initializer.node.args.args[1:]) if initializer else []
    used = set(classes) | function_names | {name for name, _ in parameters}
    instance = "_instance"
    while instance in used:
        instance += "_"
    allocation = ast.Call(func=ast.Name(id="_allocate_object", ctx=ast.Load()), args=[], keywords=[])
    allocation.allocate_class = info.name
    body = [ast.Assign(targets=[ast.Name(id=instance, ctx=ast.Store())], value=allocation)]
    if initializer:
        call = ast.Call(func=ast.Name(id=initializer.name, ctx=ast.Load()),
                        args=[ast.Name(id=instance, ctx=ast.Load())] + [ast.Name(id=name, ctx=ast.Load()) for name, _ in parameters],
                        keywords=[])
        body.append(ast.Expr(value=call))
    body.append(ast.Return(value=ast.Name(id=instance, ctx=ast.Load())))
    node = ast.FunctionDef(name=info.name,
                          args=ast.arguments(posonlyargs=[], args=arguments, vararg=None, kwonlyargs=[], kw_defaults=[], kwarg=None, defaults=[]),
                          body=body, decorator_list=[], returns=ast.Name(id=info.name, ctx=ast.Load()))
    _synthetic(node, source)
    return Function(node, list(parameters), info.name, dict(parameters), classes=classes, constructor_for=info.name)


def parse_program(tree: ast.Module, *, imported_functions=None,
                  imported_classes=None) -> Tuple[Dict[str, Function], Dict[str, ClassInfo]]:
    """Resolve all class schemas/signatures before checking any function body."""
    if not tree.body:
        raise CompileError("Write at least one function or class definition.")
    classes: Dict[str, ClassInfo] = dict(imported_classes or {})
    source_names = set()
    for node in tree.body:
        if not isinstance(node, (ast.FunctionDef, ast.ClassDef)):
            fail(node, "Only function and class definitions are allowed at the top level.")
        check_name(node.name, node)
        if node.name in source_names or node.name in classes or node.name in (imported_functions or {}):
            fail(node, "Duplicate definition '%s'." % node.name)
        source_names.add(node.name)
        if isinstance(node, ast.ClassDef):
            if node.bases or node.keywords:
                fail(node, "Class inheritance and metaclasses are not supported.")
            if node.decorator_list or getattr(node, "type_params", None):
                fail(node, "Decorators and generic type parameters are not supported.")
            classes[node.name] = ClassInfo(node.name, constructor=node.name)

    functions: Dict[str, Function] = dict(imported_functions or {})
    class_nodes: Dict[str, ast.ClassDef] = {}
    for node in tree.body:
        if isinstance(node, ast.FunctionDef):
            functions[node.name] = _function(node, classes)
            continue
        info = classes[node.name]
        class_nodes[node.name] = node
        declarations: Dict[str, ast.AST] = {}

        def declare(name: str, typ: str, declaration: ast.AST, duplicate_ok: bool = False) -> None:
            check_name(name, declaration, member=True)
            if name in info.fields and (not duplicate_ok or info.fields[name] != typ):
                fail(declaration, "Duplicate or conflicting field '%s' in class '%s'." % (name, info.name))
            info.fields[name] = typ
            declarations[name] = declaration

        # Read class-level declarations first so a matching self.field
        # declaration in __init__ is independent of member order.
        for member in node.body:
            if isinstance(member, ast.AnnAssign) and isinstance(member.target, ast.Name):
                if member.value is not None:
                    fail(member, "Declare class fields without values; initialize them in __init__.")
                declare(member.target.id, annotation(member.annotation, member, classes), member)

        for member in node.body:
            if isinstance(member, ast.Pass):
                continue
            if isinstance(member, ast.AnnAssign) and isinstance(member.target, ast.Name):
                continue
            if not isinstance(member, ast.FunctionDef):
                fail(member, "A class body may contain typed field declarations, methods, and pass only.")
            method_name = member.name
            if method_name in info.methods:
                fail(member, "Duplicate method '%s'." % method_name)
            if method_name.startswith("__") and method_name.endswith("__") and method_name != "__init__":
                fail(member, "Only the __init__ special method is supported.")
            if method_name == "__init__":
                for declaration in ast.walk(member):
                    if isinstance(declaration, ast.AnnAssign) and isinstance(declaration.target, ast.Attribute) and (
                            isinstance(declaration.target.value, ast.Name) and declaration.target.value.id == "self"):
                        declare(declaration.target.attr, annotation(declaration.annotation, declaration, classes), declaration, duplicate_ok=True)
            function = _function(member, classes, node.name)
            if function.name in source_names or function.name in functions:
                fail(member, "Generated method name '%s' conflicts with another definition." % function.name)
            functions[function.name] = function
            info.methods[method_name] = function.name
        for name in info.fields:
            if name in info.methods:
                fail(declarations[name], "Field '%s' conflicts with a method of the same name." % name)

    for name in class_nodes:
        info = classes[name]
        initializer = functions.get(info.methods.get("__init__", ""))
        functions[name] = _constructor(info, class_nodes[name], initializer, classes, set(functions))
    for function in functions.values():
        if function.name in (imported_functions or {}):
            continue
        for name, _ in function.parameters:
            if name in functions:
                fail(function.node, "A parameter cannot shadow function '%s'." % name)
        checker = Checker(functions, function)
        remaining = checker.block(function.node.body, {name for name, _ in function.parameters})
        if remaining is not None:
            if function.return_type != "None":
                fail(function.node, "Function '%s' may finish without returning a %s." % (function.name, function.return_type))
            returned = _synthetic(ast.Return(value=ast.Constant(value=None)), function.node)
            function.node.body.append(returned)
            checker.statement(returned, remaining)
    return functions, classes
