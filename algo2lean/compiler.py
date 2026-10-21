"""A non-executing, statically typed compiler to finite Lean derivations.

The generated transition relation describes finite execution prefixes.
Outputs are derived from completed valid transcripts, without a fuel bound.
"""

import ast
import io
import tokenize
from pathlib import Path
import re
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple

from .modules import generated_module_name, validate_module_name
from .frontend import CompileError, Function, fail, parse_program
from .source_types import (is_sequence, is_collection, is_finite_collection, is_dictionary,
                           sequence_element, dictionary_types, type_children, tuple_elements)
from .objects import (sequence_descriptor, collection_descriptor, collection_types, default_value, raw_type,
                      tuple_value as source_tuple, tuple_projection, uses_tuples, uses_finite_collections, uses_reals)


@dataclass
class CompilationResult:
    lean: str
    functions: List[Dict[str, Any]]
    program_lean: str
    shared_lean: str
    stats: Dict[str, int]
    module: str
    points_module: str
    points_lean: str
    namespace: Optional[str] = None
    randomized: bool = False
    probability_module: str = ""
    probability_lean: str = ""


@dataclass
class Node:
    kind: str
    line: int
    data: Any


def all_guards(*guards: Optional[str]) -> Optional[str]:
    """Definedness of a read-only expression, without duplicate premises."""
    parts = list(dict.fromkeys(guard for guard in guards if guard))
    return " ∧ ".join("(%s)" % guard for guard in parts) if parts else None


def guarded_by(condition: str, guard: Optional[str]) -> Optional[str]:
    return "(%s → %s)" % (condition, guard) if guard else None


class Lowerer:
    """Lower expressions left-to-right into an explicit control-flow graph."""

    def __init__(self, function: Function):
        self.function = function
        self.nodes: List[Node] = []
        self.point_pcs: Dict[int, int] = {}
        self.forks = {}
        self.fields = {name: "v%d" % index for index, name in enumerate(function.variables)}
        self.field_types = {self.fields[name]: typ for name, typ in function.variables.items()}
        self.field_labels = {self.fields[name]: name for name in function.variables}
        self.field_representations = {}
        if getattr(function.node, "parallel_adapter", False):
            # The fork has already captured every argument. This generated
            # forwarding boundary only needs its imported call and return.
            self.add("stuck", function.node, None)
            call = function.node.body[0].value
            target = self.temp(function.return_type)
            ret = self.add("return", function.node, self.value(target))
            self.entry = self.add("call", call, (call.resolved_name,
                [self.value(self.fields[name]) for name, _ in function.parameters],
                target, ret, None))
            return
        self.entry = self.block(function.node.body, self.add("stuck", function.node, None))

    def add(self, kind: str, source: ast.AST, data: Any) -> int:
        index = len(self.nodes)
        self.nodes.append(Node(kind, getattr(source, "lineno", 1), data))
        return index

    def temp(self, typ: str, *, representation=None) -> str:
        """Reserve a typed value, optionally with an internal snapshot representation."""
        name = "t%d" % len(self.field_types)
        self.field_types[name] = typ
        self.field_labels[name] = "temporary"
        if representation is not None:
            self.field_representations[name] = representation
        return name

    def field_representation(self, name):
        if name in self.field_representations:
            return self.field_representations[name]
        typ = self.field_types[name]
        return raw_type(typ), default_value(typ)

    def value(self, field_name: str) -> str:
        return "s.%s" % field_name

    def expression_type(self, node):
        return getattr(node, "expected_type", self.function.expression_types[id(node)])

    def convert(self, value, actual, expected):
        if actual == expected:
            return value
        if actual == "Int" and expected == "Real":
            return "((%s : Int) : Real)" % value
        actual_elements, expected_elements = tuple_elements(actual), tuple_elements(expected)
        if actual_elements is not None and expected_elements is not None:
            assert len(actual_elements) == len(expected_elements)
            return source_tuple([self.convert(tuple_projection(value, i, len(actual_elements)), a, b)
                                 for i, (a, b) in enumerate(zip(actual_elements, expected_elements))])
        if (expected in self.function.classes and self.function.classes[expected].is_interface
                and actual in self.function.classes):
            return value  # Static binding preserves the original object reference.
        if expected.endswith("?"):
            if actual == "None":
                return "none"
            if actual == expected[:-1]:
                return "(some %s)" % value
        raise AssertionError("Unsupported coercion: %s to %s" % (actual, expected))

    def object_ref(self, value, typ):
        if typ.endswith("?"):
            return "(%s).getD 0" % value, "(%s).isSome = true" % value
        return value, None

    def comparison(self, left, left_type, operator, right, right_type):
        if isinstance(operator, (ast.In, ast.NotIn)):
            return "(%s.contains h %s %s = %s)" % (collection_descriptor(right_type), right, left,
                                                    "false" if isinstance(operator, ast.NotIn) else "true")
        cls = next((typ.rstrip("?") for typ in (left_type, right_type)
                    if typ.rstrip("?") in self.function.classes), None)
        if cls is not None and left_type != right_type:
            left = self.convert(left, left_type, cls + "?")
            right = self.convert(right, right_type, cls + "?")
        symbols = {ast.Eq: "=", ast.NotEq: "≠", ast.Is: "=", ast.IsNot: "≠",
                   ast.Lt: "<", ast.LtE: "≤", ast.Gt: ">", ast.GtE: "≥"}
        return "(%s %s %s)" % (left, symbols[type(operator)], right)

    def field_read(self, node, receiver):
        typ = self.expression_type(node.value)
        cls = typ.rstrip("?")
        ref, guard = self.object_ref(receiver, typ)
        field = "(field_%s_%s h (%s))" % (cls, node.attr, ref)
        from .objects import default_value
        return "(%s.getD %s)" % (field, default_value(self.function.expression_types[id(node)])), all_guards(guard, "%s.isSome = true" % field)

    def sequence_read(self, typ, ref, index):
        if typ == "Seq":
            return "(h.read %s %s)" % (ref, index), "%s < h.nextRef" % ref
        value = "(%s.get h %s %s)" % (sequence_descriptor(typ), ref, index)
        return "(%s.getD %s)" % (value, default_value(sequence_element(typ))), "%s.isSome = true" % value

    def dictionary_read(self, typ, ref, key):
        descriptor = collection_descriptor(typ)
        value = "(%s.get h %s %s)" % (descriptor, ref, key)
        return "(%s.getD %s)" % (value, default_value(dictionary_types(typ)[1])), all_guards(
            "%s.valid h %s" % (descriptor, ref), "%s.isSome = true" % value)

    def collection_call(self, node, target, following):
        """Evaluate a finite-container receiver and its arguments exactly once."""
        operation = node.collection_operation
        receiver = getattr(node, "receiver", None)
        arguments = ([receiver] if receiver is not None else []) + node.args
        temps = [self.temp(self.expression_type(argument)) for argument in arguments]
        values = [self.value(temp) for temp in temps]
        typ = self.expression_type(arguments[0])
        descriptor = collection_descriptor(typ)
        valid = "%s.valid h %s" % (descriptor, values[0])
        if operation == "copy":
            allocation = "(%s.copy h %s)" % (descriptor, values[0])
            tail = self.add("sequence_allocate", node, (target, allocation, following, valid))
        elif operation == "length":
            tail = self.assign(target, "(Int.ofNat (%s.size h %s))" % (descriptor, values[0]), following, node, valid)
        elif operation == "dict_get":
            value = "((%s.get h %s %s).getD %s)" % (descriptor, *values)
            tail = self.assign(target, self.convert(value, self.function.expression_types[id(node)], self.field_types[target]),
                               following, node, valid)
        else:
            method = {"set_add": "insert", "set_discard": "erase"}[operation]
            heap = "(%s.%s h %s %s)" % (descriptor, method, *values)
            tail = self.add("heap_update", node, (heap, target, "()", following, valid))
        for argument, temp in reversed(list(zip(arguments[1:], temps[1:]))):
            tail = self.expr(argument, temp, tail)
        if receiver is not None:
            # Bound-method lookup occurs before arguments can mutate the heap.
            tail = self.assign(temps[0], values[0], tail, node, valid)
        return self.expr(arguments[0], temps[0], tail)

    def collection_literal(self, node, target, following):
        typ = self.expression_type(node)
        arguments = (node.elts if isinstance(node, ast.Set) else
                     [part for pair in zip(node.keys, node.values) for part in pair]
                     if isinstance(node, ast.Dict) else [])
        pure = [self.pure_expr(argument) for argument in arguments]
        if all(value is not None for value in pure):
            values = [value for value, _ in pure]
            entries = (values if not is_dictionary(typ) else
                       ["(%s, %s)" % pair for pair in zip(values[::2], values[1::2])])
            allocation = "(%s.create h [%s])" % (collection_descriptor(typ), ", ".join(entries))
            return self.add("sequence_allocate", node,
                (target, allocation, following, all_guards(*(guard for _, guard in pure))))
        temps = [self.temp(self.expression_type(argument)) for argument in arguments]
        values = [self.value(temp) for temp in temps]
        entries = (values if not is_dictionary(typ) else
                   ["(%s, %s)" % pair for pair in zip(values[::2], values[1::2])])
        allocation = "(%s.create h [%s])" % (collection_descriptor(typ), ", ".join(entries))
        tail = self.add("sequence_allocate", node, (target, allocation, following, None))
        for argument, temp in reversed(list(zip(arguments, temps))):
            tail = self.expr(argument, temp, tail)
        return tail

    def sequence_write(self, typ, source, data):
        if is_dictionary(typ):
            ref, key, value, target, following, expression_guard = data
            descriptor = collection_descriptor(typ)
            guard = all_guards(expression_guard, "%s.valid h %s" % (descriptor, ref))
            heap = "(%s.set h %s %s %s)" % (descriptor, ref, key, value)
            return self.add("heap_update", source, (heap, target, ref, following, guard))
        return self.add("sequence_write", source, (typ, data)) if is_collection(typ) else self.add("write", source, data)

    def assign(self, target: str, expr: str, following: int, source: ast.AST,
               guard: Optional[str] = None) -> int:
        return self.add("assign", source, (target, expr, following, guard))

    def binary(self, op: ast.operator, left: str, right: str) -> Tuple[str, Optional[str]]:
        a, b = self.value(left), self.value(right)
        if isinstance(op, ast.Div):
            return "(%s / %s)" % (a, b), "%s ≠ 0" % b
        if isinstance(op, ast.FloorDiv):
            return "(Int.fdiv %s %s)" % (a, b), "%s ≠ 0" % b
        if isinstance(op, ast.Mod):
            return "(Int.fmod %s %s)" % (a, b), "%s ≠ 0" % b
        symbol = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*"}[type(op)]
        return "(%s %s %s)" % (a, symbol, b), None

    def pure_expr(self, node: ast.AST) -> Optional[Tuple[str, Optional[str]]]:
        result = self._pure_expr(node)
        if result is None:
            return None
        return self.convert(result[0], self.function.expression_types[id(node)], self.expression_type(node)), result[1]

    def _pure_expr(self, node: ast.AST) -> Optional[Tuple[str, Optional[str]]]:
        """A read-only expression and the exact condition under which it is defined.

        All observations use the same heap and locals. This helper returns None
        for calls, allocations, and mutations so the caller lowers their effects
        in evaluation order. Conditional guards preserve source short-circuiting
        even though Lean operations are total.
        """
        if isinstance(node, ast.Constant):
            if node.value is None:
                return "()", None
            if type(node.value) is bool:
                return ("true" if node.value else "false"), None
            if type(node.value) is float:
                from .real_literals import real_literal_ratio
                numerator, denominator = real_literal_ratio(node)
                return "(%s / %s : Real)" % (numerator, denominator), None
            # Comparisons must not infer Nat arithmetic for literal-only terms.
            return "(%s : Int)" % node.value, None
        if isinstance(node, ast.Name):
            return self.value(self.fields[node.id]), None
        if isinstance(node, ast.Tuple):
            values = [self.pure_expr(element) for element in node.elts]
            if any(value is None for value in values):
                return None
            return source_tuple([value for value, _ in values]), all_guards(*(guard for _, guard in values))
        if isinstance(node, ast.UnaryOp):
            value = self.pure_expr(node.operand)
            if value is None:
                return None
            if isinstance(node.op, ast.UAdd):
                return value
            return "(%s%s)" % ("!" if isinstance(node.op, ast.Not) else "-", value[0]), value[1]
        if isinstance(node, ast.BinOp):
            left, right = self.pure_expr(node.left), self.pure_expr(node.right)
            if left is None or right is None:
                return None
            if isinstance(node.op, ast.Div):
                return "(%s / %s)" % (left[0], right[0]), all_guards(left[1], right[1], "%s ≠ 0" % right[0])
            if isinstance(node.op, (ast.FloorDiv, ast.Mod)):
                operation = "Int.fdiv" if isinstance(node.op, ast.FloorDiv) else "Int.fmod"
                return "(%s %s %s)" % (operation, left[0], right[0]), all_guards(left[1], right[1], "%s ≠ 0" % right[0])
            return "(%s %s %s)" % (left[0], {ast.Add: "+", ast.Sub: "-", ast.Mult: "*"}[type(node.op)], right[0]), all_guards(left[1], right[1])
        if isinstance(node, ast.BoolOp):
            values = [self.pure_expr(value) for value in node.values]
            if any(value is None for value in values):
                return None
            is_and = isinstance(node.op, ast.And)
            guards, previous = [], []
            for value, guard in values:
                guards.append(guarded_by(" ∧ ".join(previous), guard) if previous else guard)
                previous.append("%s = %s" % (value, "true" if is_and else "false"))
            return "(%s)" % (" && " if is_and else " || ").join(value for value, _ in values), all_guards(*guards)
        if isinstance(node, ast.Compare):
            operands = [node.left] + node.comparators
            values = [self.pure_expr(value) for value in operands]
            if any(value is None for value in values):
                return None
            terms = [self.comparison(values[i][0], self.expression_type(operands[i]), op,
                                    values[i + 1][0], self.expression_type(operands[i + 1]))
                     for i, op in enumerate(node.ops)]
            guards = [values[0][1], values[1][1]]
            for index in range(2, len(values)):
                guards.append(guarded_by(" ∧ ".join(terms[:index - 1]), values[index][1]))
            for index, op in enumerate(node.ops):
                if isinstance(op, (ast.In, ast.NotIn)):
                    guard = "%s.valid h %s" % (collection_descriptor(self.expression_type(operands[index + 1])), values[index + 1][0])
                    guards.append(guarded_by(" ∧ ".join(terms[:index]), guard) if index else guard)
            return "(decide (%s))" % " ∧ ".join(terms), all_guards(*guards)
        if isinstance(node, ast.IfExp):
            condition, yes, no = self.pure_expr(node.test), self.pure_expr(node.body), self.pure_expr(node.orelse)
            if condition is None or yes is None or no is None:
                return None
            return "(if %s then %s else %s)" % (condition[0], yes[0], no[0]), all_guards(
                condition[1], guarded_by("%s = true" % condition[0], yes[1]),
                guarded_by("%s = false" % condition[0], no[1]))
        if isinstance(node, ast.Subscript):
            if hasattr(node, "tuple_index"):
                value = self.pure_expr(node.value)
                if value is None:
                    return None
                arity = len(tuple_elements(self.expression_type(node.value)))
                return tuple_projection(value[0], node.tuple_index, arity), value[1]
            sequence, index = self.pure_expr(node.value), self.pure_expr(node.slice)
            if sequence is None or index is None:
                return None
            typ = self.expression_type(node.value)
            read = self.dictionary_read if is_dictionary(typ) else self.sequence_read
            value, guard = read(typ, sequence[0], index[0])
            return value, all_guards(sequence[1], index[1], guard)
        if isinstance(node, ast.Attribute):
            receiver = self.pure_expr(node.value)
            if receiver is None:
                return None
            value, guard = self.field_read(node, receiver[0])
            return value, all_guards(receiver[1], guard)
        if isinstance(node, ast.Call) and getattr(node, "real_conversion", False):
            return self.pure_expr(node.args[0])
        if isinstance(node, ast.Call) and getattr(node, "collection_operation", None) in {"length", "dict_get"}:
            arguments = ([node.receiver] if hasattr(node, "receiver") else []) + node.args
            values = [self.pure_expr(argument) for argument in arguments]
            if any(value is None for value in values):
                return None
            descriptor = collection_descriptor(self.expression_type(arguments[0]))
            terms = [value for value, _ in values]
            value = ("(Int.ofNat (%s.size h %s))" % (descriptor, terms[0]) if node.collection_operation == "length"
                     else "((%s.get h %s %s).getD %s)" % (descriptor, *terms))
            return value, all_guards(*(guard for _, guard in values), "%s.valid h %s" % (descriptor, terms[0]))
        return None

    def expr(self, node: ast.AST, target: str, following: int) -> int:
        if getattr(node, "fork_join", False):
            # Freeze every argument before either branch starts. The ordinary
            # Step relation is the left-to-right serialization; the parallel
            # semantics recognizes the same call boundary via this metadata.
            children = node.args
            outputs = [self.temp(self.expression_type(child)) for child in children]
            args = [[self.temp(self.expression_type(arg)) for arg in child.args] for child in children]
            finish = self.assign(target, source_tuple([self.value(out) for out in outputs]), following, node)
            right = self.add("call", children[1], (children[1].resolved_name,
                [self.value(arg) for arg in args[1]], outputs[1], finish, None))
            left = self.add("call", children[0], (children[0].resolved_name,
                [self.value(arg) for arg in args[0]], outputs[0], right, None))
            self.forks[left] = (right, finish)
            tail = left
            for child, slots in reversed(list(zip(children, args))):
                for argument, slot in reversed(list(zip(child.args, slots))):
                    tail = self.expr(argument, slot, tail)
            return tail
        value = self.pure_expr(node)
        if value is not None:
            return self.assign(target, self.convert(value[0], self.expression_type(node), self.field_types[target]), following, node, value[1])
        if isinstance(node, ast.Call) and getattr(node, "real_conversion", False):
            return self.expr(node.args[0], target, following)
        if isinstance(node, (ast.Set, ast.Dict)) or (isinstance(node, ast.Call) and
                isinstance(node.func, ast.Name) and node.func.id == "set"):
            return self.collection_literal(node, target, following)
        if isinstance(node, ast.Call) and getattr(node, "collection_operation", None):
            return self.collection_call(node, target, following)
        if isinstance(node, ast.Tuple):
            temps = [self.temp(self.expression_type(element)) for element in node.elts]
            value = source_tuple([self.value(temp) for temp in temps])
            tail = self.assign(target, self.convert(value, self.expression_type(node), self.field_types[target]), following, node)
            for element, temp in reversed(list(zip(node.elts, temps))):
                tail = self.expr(element, temp, tail)
            return tail
        if isinstance(node, ast.UnaryOp):
            operand = self.temp(self.expression_type(node.operand))
            symbol = {ast.Not: "!", ast.USub: "-", ast.UAdd: "+"}[type(node.op)]
            value = self.value(operand) if symbol == "+" else "(%s%s)" % (symbol, self.value(operand))
            value = self.convert(value, self.function.expression_types[id(node)], self.field_types[target])
            return self.expr(node.operand, operand, self.assign(target, value, following, node))
        if isinstance(node, ast.BinOp):
            left, right = self.temp(self.expression_type(node.left)), self.temp(self.expression_type(node.right))
            value, guard = self.binary(node.op, left, right)
            value = self.convert(value, self.function.expression_types[id(node)], self.field_types[target])
            tail = self.assign(target, value, following, node, guard)
            return self.expr(node.left, left, self.expr(node.right, right, tail))
        if isinstance(node, ast.BoolOp):
            tail = self.expr(node.values[-1], target, following)
            for value in reversed(node.values[:-1]):
                yes, no = (tail, following) if isinstance(node.op, ast.And) else (following, tail)
                branch = self.add("branch", node, (self.value(target), yes, no))
                tail = self.expr(value, target, branch)
            return tail
        if isinstance(node, ast.Compare):
            operands = [node.left] + node.comparators
            temps = [self.temp(self.expression_type(value)) for value in operands]
            tail = self.assign(target, "true", following, node)
            false = self.assign(target, "false", following, node)
            for index in reversed(range(len(node.ops))):
                comparison = self.comparison(self.value(temps[index]), self.field_types[temps[index]], node.ops[index],
                                             self.value(temps[index + 1]), self.field_types[temps[index + 1]])
                condition = "(decide %s)" % comparison
                if isinstance(node.ops[index], (ast.In, ast.NotIn)):
                    valid = "%s.valid h %s" % (collection_descriptor(self.field_types[temps[index + 1]]), self.value(temps[index + 1]))
                    branch = self.add("branch", node, (self.value(target), tail, false))
                    branch = self.assign(target, condition, branch, node, valid)
                else:
                    branch = self.add("branch", node, (condition, tail, false))
                tail = self.expr(operands[index + 1], temps[index + 1], branch)
            return self.expr(operands[0], temps[0], tail)
        if isinstance(node, ast.IfExp):
            condition = self.temp("Bool")
            branch = self.add("branch", node, (self.value(condition), self.expr(node.body, target, following), self.expr(node.orelse, target, following)))
            return self.expr(node.test, condition, branch)
        if isinstance(node, ast.Subscript):
            typ = self.expression_type(node.value)
            if hasattr(node, "tuple_index"):
                product = self.temp(typ)
                value = tuple_projection(self.value(product), node.tuple_index, len(tuple_elements(typ)))
                value = self.convert(value, self.function.expression_types[id(node)], self.field_types[target])
                return self.expr(node.value, product, self.assign(target, value, following, node))
            sequence, index = self.temp(typ), self.temp(dictionary_types(typ)[0] if is_dictionary(typ) else "Int")
            read = self.dictionary_read if is_dictionary(typ) else self.sequence_read
            value, guard = read(typ, self.value(sequence), self.value(index))
            value = self.convert(value, self.function.expression_types[id(node)], self.field_types[target])
            tail = self.assign(target, value, following, node, guard)
            return self.expr(node.value, sequence, self.expr(node.slice, index, tail))
        if isinstance(node, ast.Attribute):
            receiver = self.temp(self.expression_type(node.value))
            value, guard = self.field_read(node, self.value(receiver))
            value = self.convert(value, self.function.expression_types[id(node)], self.field_types[target])
            return self.expr(node.value, receiver, self.assign(target, value, following, node, guard))
        if isinstance(node, ast.Call):
            if getattr(node, "allocate_class", None):
                return self.add("object_allocate", node, (node.allocate_class, target, following))
            name = getattr(node, "resolved_name", None) or node.func.id
            receiver = getattr(node, "receiver", None)
            arguments = ([receiver] if receiver is not None else []) + node.args
            args = [self.temp(self.expression_type(value)) for value in arguments]
            values = [self.value(arg) for arg in args]
            guard = None
            if receiver is not None:
                cls = self.expression_type(receiver).rstrip("?")
                ref, nonnull = self.object_ref(values[0], self.expression_type(receiver))
                values[0] = "(%s)" % ref
                guard = all_guards(nonnull, "is_%s h %s" % (cls, values[0]))
            if name == "const":
                typ = self.expression_type(node)
                if is_collection(typ):
                    allocation = "(%s.const h %s)" % (sequence_descriptor(typ), values[0])
                    tail = self.add("sequence_allocate", node, (target, allocation, following, None))
                else:
                    tail = self.add("allocate", node, (target, "(fun _ => %s)" % values[0], following, None))
            elif name == "copy":
                typ = self.expression_type(node)
                if is_collection(typ):
                    allocation = "(%s.copy h %s)" % (sequence_descriptor(typ), values[0])
                    tail = self.add("sequence_allocate", node, (target, allocation, following,
                        "%s.valid h %s" % (sequence_descriptor(typ), values[0])))
                else:
                    tail = self.add("allocate", node, (target, "(h.store %s)" % values[0], following, "%s < h.nextRef" % values[0]))
            elif name == "update":
                tail = self.sequence_write(self.expression_type(node), node,
                    (values[0], values[1], values[2], target, following, None))
            elif name == "randint":
                tail = self.add("random", node, (target, values[0], values[1], following))
            else:
                tail = self.add("call", node, (name, values, target, following, None))
            for value, arg in reversed(list(zip(arguments[1:] if receiver is not None else arguments,
                                                args[1:] if receiver is not None else args))):
                tail = self.expr(value, arg, tail)
            if receiver is not None:
                # Bound-method lookup precedes argument evaluation, even when
                # the receiver is invalid or None.
                tail = self.assign(args[0], self.value(args[0]), tail, node, guard)
                tail = self.expr(receiver, args[0], tail)
            return tail
        raise AssertionError("Type checker accepted an unknown expression")

    def block(self, statements: List[ast.stmt], following: int) -> int:
        for node in reversed(statements):
            following = self.statement(node, following)
        return following

    def statement(self, node: ast.stmt, following: int) -> int:
        entry = self._statement(node, following)
        if id(node) in self.function.points:
            self.point_pcs[id(node)] = entry
        return entry

    def _statement(self, node: ast.stmt, following: int) -> int:
        if isinstance(node, ast.Return):
            target = self.temp(self.function.return_type)
            ret = self.add("return", node, self.value(target))
            return self.expr(node.value, target, ret)
        if isinstance(node, ast.Pass):
            return self.add("noop", node, following)
        if isinstance(node, (ast.Assign, ast.AnnAssign)):
            target = node.targets[0] if isinstance(node, ast.Assign) else node.target
            if isinstance(target, ast.Tuple):
                typ = self.expression_type(node.value)
                result = self.temp(typ)
                assignments = []
                def unpack(pattern, value, actual):
                    if isinstance(pattern, ast.Name):
                        expected = self.function.variables[pattern.id]
                        assignments.append((self.fields[pattern.id], self.convert(value, actual, expected)))
                        return
                    elements = tuple_elements(actual)
                    for i, (child, element) in enumerate(zip(pattern.elts, elements)):
                        unpack(child, tuple_projection(value, i, len(elements)), element)
                unpack(target, self.value(result), typ)
                tail = following
                for field, value in reversed(assignments):
                    tail = self.assign(field, value, tail, node)
                return self.expr(node.value, result, tail)
            if isinstance(target, ast.Name):
                value = self.pure_expr(node.value)
                if value is not None:
                    return self.assign(self.fields[target.id], self.convert(value[0], self.expression_type(node.value), self.function.variables[target.id]), following, node, value[1])
                result = self.temp(self.function.variables[target.id])
                commit = self.assign(self.fields[target.id], self.value(result), following, node)
                return self.expr(node.value, result, commit)
            if isinstance(target, ast.Attribute):
                cls = self.expression_type(target.value).rstrip("?")
                value, owner = self.pure_expr(node.value), self.pure_expr(target.value)
                if value is not None and owner is not None:
                    ref, nonnull = self.object_ref(owner[0], self.expression_type(target.value))
                    return self.add("field_write", node, (cls, target.attr, ref, value[0], following,
                        all_guards(value[1], owner[1], nonnull)))
                result = self.temp(self.function.classes[cls].fields[target.attr])
                receiver = self.temp(self.expression_type(target.value))
                ref, guard = self.object_ref(self.value(receiver), self.expression_type(target.value))
                tail = self.add("field_write", node, (cls, target.attr, ref, self.value(result), following, guard))
                return self.expr(node.value, result, self.expr(target.value, receiver, tail))
            value, sequence_value, position = self.pure_expr(node.value), self.pure_expr(target.value), self.pure_expr(target.slice)
            typ = self.expression_type(target.value)
            if value is not None and position is not None and sequence_value is not None:
                return self.sequence_write(typ, node, (sequence_value[0], position[0],
                    value[0], None, following, all_guards(value[1], sequence_value[1], position[1])))
            # As in Python, the RHS is evaluated before the assignment index.
            key_type, element_type = dictionary_types(typ) if is_dictionary(typ) else ("Int", sequence_element(typ))
            result, index, sequence = self.temp(element_type), self.temp(key_type), self.temp(typ)
            update = self.sequence_write(typ, node, (self.value(sequence), self.value(index), self.value(result), None, following, None))
            # Python evaluates RHS, then the target object, then the target index.
            if isinstance(target.value, ast.Name):
                capture = self.assign(sequence, self.value(self.fields[target.value.id]), self.expr(target.slice, index, update), node)
            else:
                capture = self.expr(target.value, sequence, self.expr(target.slice, index, update))
            return self.expr(node.value, result, capture)
        if isinstance(node, ast.Delete):
            target = node.targets[0]
            typ = self.expression_type(target.value)
            descriptor = collection_descriptor(typ)
            ref, key = self.temp(typ), self.temp(dictionary_types(typ)[0])
            guard = all_guards("%s.valid h %s" % (descriptor, self.value(ref)),
                               "%s.contains h %s %s = true" % (descriptor, self.value(ref), self.value(key)))
            heap = "(%s.erase h %s %s)" % (descriptor, self.value(ref), self.value(key))
            tail = self.add("heap_update", node, (heap, None, None, following, guard))
            return self.expr(target.value, ref, self.expr(target.slice, key, tail))
        if isinstance(node, ast.AugAssign):
            if isinstance(node.target, ast.Attribute):
                attribute = node.target
                cls = self.expression_type(attribute.value).rstrip("?")
                receiver = self.temp(self.expression_type(attribute.value))
                left, right = self.temp(self.function.expression_types[id(attribute)]), self.temp(self.expression_type(node.value))
                term, operation_guard = self.binary(node.op, left, right)
                ref, nonnull = self.object_ref(self.value(receiver), self.expression_type(attribute.value))
                tail = self.add("field_write", node, (cls, attribute.attr, ref, term, following,
                    all_guards(nonnull, operation_guard)))
                rhs = self.expr(node.value, right, tail)
                old, guard = self.field_read(attribute, self.value(receiver))
                read = self.assign(left, old, rhs, node, guard)
                return self.expr(attribute.value, receiver, read)
            value = self.pure_expr(node.value)
            if value is not None:
                field = self.fields[node.target.id]
                term, guard = value
                if isinstance(node.op, (ast.FloorDiv, ast.Mod)):
                    operation = "Int.fdiv" if isinstance(node.op, ast.FloorDiv) else "Int.fmod"
                    guard = all_guards(guard, "%s ≠ 0" % term)
                    term = "(%s %s %s)" % (operation, self.value(field), term)
                else:
                    if isinstance(node.op, ast.Div):
                        guard = all_guards(guard, "%s ≠ 0" % term)
                    term = "(%s %s %s)" % (self.value(field), {ast.Add: "+", ast.Sub: "-", ast.Mult: "*", ast.Div: "/"}[type(node.op)], term)
                return self.assign(field, term, following, node, guard)
            left, right = self.temp(self.function.variables[node.target.id]), self.temp(self.expression_type(node.value))
            value, guard = self.binary(node.op, left, right)
            tail = self.assign(self.fields[node.target.id], value, following, node, guard)
            return self.expr(node.target, left, self.expr(node.value, right, tail))
        if isinstance(node, ast.If):
            condition = self.temp("Bool")
            yes, no = self.block(node.body, following), self.block(node.orelse, following)
            branch = self.add("branch", node, (self.value(condition), yes, no))
            return self.expr(node.test, condition, branch)
        if isinstance(node, ast.While):
            condition = self.temp("Bool")
            branch = self.add("branch", node, None)
            entry = self.expr(node.test, condition, branch)
            body = self.block(node.body, entry)
            self.nodes[branch].data = (self.value(condition), body, following)
            return entry
        if isinstance(node, ast.For):
            if hasattr(node, "collection_iteration"):
                typ = self.expression_type(node.iter)
                key = type_children(typ)[0]
                descriptor = collection_descriptor(typ)
                receiver = self.temp(typ)
                snapshot = self.temp(key, representation=("List %s" % raw_type(key), "[]"))
                test = self.add("branch", node, None)
                advance = self.assign(snapshot, "%s.tail" % self.value(snapshot), test, node)
                body = self.block(node.body, advance)
                element = "(%s.headD %s)" % (self.value(snapshot), default_value(key))
                bind = self.assign(self.fields[node.target.id], self.convert(element, key,
                    self.function.variables[node.target.id]), body, node)
                self.nodes[test].data = ("(!%s.isEmpty)" % self.value(snapshot), bind, following)
                capture = self.assign(snapshot, "(%s.keys h %s)" % (descriptor, self.value(receiver)), test, node,
                    "%s.valid h %s" % (descriptor, self.value(receiver)))
                return self.expr(node.iter, receiver, capture)
            current, stop, step = self.temp("Int"), self.temp("Int"), self.temp("Int")
            test = self.add("branch", node, None)
            increment = self.assign(current, "(%s + %s)" % (self.value(current), self.value(step)), test, node)
            body = self.block(node.body, increment)
            bind = self.assign(self.fields[node.target.id], self.convert(self.value(current), "Int", self.function.variables[node.target.id]), body, node)
            condition = "(decide ((%s > 0 ∧ %s < %s) ∨ (%s < 0 ∧ %s > %s)))" % (self.value(step), self.value(current), self.value(stop), self.value(step), self.value(current), self.value(stop))
            self.nodes[test].data = (condition, bind, following)
            tail = self.assign(step, self.value(step), test, node, "%s ≠ 0" % self.value(step))
            args = node.iter.args
            if len(args) == 1:
                tail = self.assign(step, "1", tail, node)
                tail = self.assign(current, "0", tail, node)
                return self.expr(args[0], stop, tail)
            if len(args) == 2:
                tail = self.assign(step, "1", tail, node)
            else:
                tail = self.expr(args[2], step, tail)
            return self.expr(args[0], current, self.expr(args[1], stop, tail))
        if isinstance(node, ast.Expr):
            if hasattr(node, "clock_name"):
                amount = node.tick_amount
                if amount is None or (isinstance(amount, ast.Constant) and amount.value >= 0):
                    return self.add("tick", node, (node.clock_name, str(amount.value) if amount else "1", following, None))
                value = self.pure_expr(amount)
                if value is not None:
                    return self.add("tick", node, (node.clock_name, "(%s).toNat" % value[0], following,
                        all_guards(value[1], "0 ≤ %s" % value[0])))
                target = self.temp("Int")
                tail = self.add("tick", node, (node.clock_name, "%s.toNat" % self.value(target), following,
                    "0 ≤ %s" % self.value(target)))
                return self.expr(amount, target, tail)
            return self.expr(node.value, self.temp(self.function.expression_types[id(node.value)]), following)
        raise AssertionError("Type checker accepted an unknown statement")


def assign_points(functions: Dict[str, Function], source: str) -> None:
    """Name a statement's entry with a standalone label directly above it."""
    from .public_names import function_namespace, identifier
    if "@" not in source:
        return
    statements = []
    for function in functions.values():
        statements.extend((node, function) for node in ast.walk(function.node)
                          if id(node) in function.assigned_at)
    statements.sort(key=lambda pair: (pair[0].lineno, pair[0].col_offset))
    labels = {}
    source_lines = source.splitlines()
    for token in tokenize.generate_tokens(io.StringIO(source).readline):
        if token.type != tokenize.COMMENT or not token.string[1:].strip().startswith("@"):
            continue
        match = re.fullmatch(r"#\s*@([A-Za-z_][A-Za-z_0-9]*)\s*", token.string)
        if not match:
            raise CompileError("A point label must be a standalone comment such as # @update.", token.start[0], token.start[1] + 1)
        row, column = token.start
        if source_lines[row - 1][:column].strip():
            raise CompileError("Put # @%s on its own line immediately before the statement, at the same indentation. Labels refer to the state before execution." % match.group(1), row, column + 1)
        candidates = [pair for pair in statements
                      if pair[0].lineno == row + 1 and pair[0].col_offset == column]
        if len(candidates) != 1:
            raise CompileError("Put the label immediately above one statement at the same indentation, with no intervening blank or comment lines.", row, column + 1)
        node = candidates[0][0]
        if id(node) in labels:
            fail(node, "A statement cannot have more than one label.")
        labels[id(node)] = match.group(1)
    used = {name: set() for name in functions}
    for node, function in statements:
        if id(node) not in labels:
            continue
        name = labels[id(node)]
        if name in used[function.name]:
            fail(node, "Duplicate source point name '%s' in function '%s'." % (name, function.name))
        used[function.name].add(name)
        initialized = function.assigned_at[id(node)]
        function.points[id(node)] = {
            "name": name, "line": node.lineno, "column": node.col_offset + 1,
            "end_line": getattr(node, "end_lineno", node.lineno),
            "variables": [{"name": variable, "type": typ}
                          for variable, typ in function.variables.items() if variable in initialized],
            "relation": function_namespace(function) + ".At." + identifier(name),
        }


def validate_generated_names(functions: Dict[str, Function], *, probability=False) -> None:
    from .public_names import public_aliases, point_aliases
    symbols = set()
    has_clocks = any(function.clocks for function in functions.values())
    def reserve(name: str, node: ast.AST) -> None:
        if name in symbols:
            fail(node, "Generated Lean name '%s' is ambiguous; rename the function, variable, or label." % name)
        symbols.add(name)
    for typ in collection_types(functions.values()):
        reserve(collection_descriptor(typ), next(iter(functions.values())).node)
    for cls, definition in next(iter(functions.values())).classes.items():
        node = (functions[cls] if cls in functions else
                functions[next(iter(definition.methods.values()))]).node
        for name in ("Ref_" + cls, "is_" + cls, "create_" + cls):
            reserve(name, node)
        for field_name in definition.fields:
            for name in ("field_%s_%s" % (cls, field_name), "set_%s_%s" % (cls, field_name),
                         "field_%s_%s_set" % (cls, field_name)):
                reserve(name, node)
    for function in functions.values():
        for public, _ in public_aliases(function, has_clocks) + point_aliases(function):
            reserve(public, function.node)
    if probability:
        validate_probability_names(functions)


def validate_probability_names(functions: Dict[str, Function]) -> None:
    """Check a companion's public names without requiring imported declarations.

    Project modules already validate core names with their imported classes.
    Companion facades may contain no locally defined functions at all.
    """
    from .public_names import PROBABILITY_MEMBERS, function_namespace, public_aliases, point_aliases
    has_clocks = any(function.clocks for function in functions.values())
    symbols = {public for function in functions.values()
               for public, _ in public_aliases(function, has_clocks) + point_aliases(function)}
    probability_names = {function_namespace(function) + "." + member
                         for function in functions.values() for member in PROBABILITY_MEMBERS}
    for function in functions.values():
        namespace = function_namespace(function)
        if namespace in probability_names:
            fail(function.node, "Generated Lean name '%s' conflicts with a probability declaration; rename the method." % namespace)
        for member in PROBABILITY_MEMBERS:
            name = namespace + "." + member
            if name in symbols:
                fail(function.node, "Generated Lean name '%s' is ambiguous; rename the function, variable, or label." % name)
            symbols.add(name)


def emit(functions: Dict[str, Function], module: str, namespace: str = "", *, lowered=None) -> Tuple[str, str, str]:
    from .emitter import emit_program, emit_points_module
    if lowered is None:
        lowered = {name: Lowerer(function) for name, function in functions.items()}
    shared = (Path(__file__).resolve().parent.parent / "Algo2Lean.lean").read_text(encoding="utf-8")
    return emit_program(lowered, namespace), shared, emit_points_module(lowered, module, namespace)


def compile_source(source: str, filename: str = "<input>", *, standalone: bool = False,
                   module: Optional[str] = None, namespace: Optional[str] = None) -> CompilationResult:
    """Compile source to direct transitions and transcript-derived Lean outputs.

    ``lean`` contains stable algorithm definitions, independent of line labels.
    ``points_lean`` imports those definitions and adds the named-line interface.
    ``module`` is the general file's Lean module name; by default it is safely
    derived from ``filename``. Function metadata is JSON compatible.
    ``namespace`` optionally isolates the complete generated interface so a
    separately proved component can be imported alongside its calling program.
    """
    if type(standalone) is not bool:
        raise CompileError("standalone must be true or false.")
    if not isinstance(source, str):
        raise CompileError("Source must be text.")
    if not isinstance(filename, str) or any(character == "\x00" or 0xD800 <= ord(character) <= 0xDFFF for character in filename):
        raise CompileError("Filename must be valid text without null characters.")
    try:
        module = validate_module_name(generated_module_name(filename) if module is None else module)
        if namespace is not None:
            validate_module_name(namespace)
            if namespace in {"Algo2LeanGenerated", "Algo2LeanCore", "Algo2LeanParallel"}:
                raise ValueError("The generated namespace must be distinct from the runtime namespaces.")
    except ValueError as error:
        raise CompileError(str(error)) from None
    from .source_validation import parse_source
    from .publication import credit_generated
    try:
        tree = parse_source(source, filename)
        functions, classes = parse_program(tree)
        from .parallel import validate_parallel
        parallel = validate_parallel(functions)
        assign_points(functions, source)
        validate_generated_names(functions)
        lowered = {name: Lowerer(function) for name, function in functions.items()}
        from .parallel import parallel_functions, require_parallel
        parallel_admitted = parallel_functions(lowered) if parallel else set()
        require_parallel(lowered, parallel_admitted)
        program_lean, shared_lean, points_lean = emit(functions, module, "«%s»" % namespace if namespace else "", lowered=lowered)
        program_lean = credit_generated(program_lean)
        if namespace is not None:
            prefix = "namespace «%s»\n\nopen _root_.Algo2LeanGenerated\n\n" % namespace
            suffix = "\nend «%s»\n" % namespace
            program_lean = prefix + program_lean + suffix
            imports, body = points_lean.split("\n", 1)
            points_lean = imports + "\n\n" + prefix + body + suffix
        points_lean = credit_generated(points_lean)
        tuple_support = uses_tuples(functions.values())
        finite_support = uses_finite_collections(functions.values())
        real_support = uses_reals(functions.values())
        if standalone:
            support = ""
            if finite_support or real_support:
                from .checker import _library_sources
                sources = _library_sources(("Algo2LeanLib.FiniteCollections" if finite_support else "Algo2LeanLib.Tuple",))
                support = "\n".join("\n".join(line for line in text.decode("utf-8").splitlines()
                    if not line.startswith("import ")) for name, (_, text) in sources.items() if name != "Algo2Lean") + "\n"
            elif tuple_support:
                path = Path(__file__).resolve().parent.parent / "Algo2LeanLib/Tuple.lean"
                support = path.read_text(encoding="utf-8").removeprefix("import Algo2Lean\n")
            if parallel:
                support += "\n" + (Path(__file__).resolve().parent.parent / "Algo2LeanLib/Parallel.lean").read_text(encoding="utf-8").removeprefix("import Algo2Lean\n")
            if real_support:
                real_source = (Path(__file__).resolve().parent.parent / "probability/Algo2LeanReal.lean").read_text(encoding="utf-8")
                external = "\n".join(line for line in real_source.splitlines() if line.startswith("import Mathlib"))
                support += "\n" + "\n".join(line for line in real_source.splitlines() if not line.startswith("import ")) + "\n"
                lean = external + "\n" + shared_lean + "\n" + support + program_lean
            else:
                lean = shared_lean + "\n" + support + program_lean
        else:
            dependency = ("Algo2LeanLib.FiniteCollections" if finite_support else
                          "Algo2LeanLib.Tuple" if tuple_support else "Algo2Lean")
            dependencies = [dependency] + (["Algo2LeanReal"] if real_support else []) + (["Algo2LeanLib.Parallel"] if parallel else [])
            lean = "\n".join("import " + name for name in dependencies) + "\n\n" + program_lean
        from .emitter import public_types
        from .public_names import interface_metadata
        from .probability import emit_probability, has_randomness
        randomized = has_randomness(lowered)
        if randomized:
            validate_generated_names(functions, probability=True)
        clocks = sorted(set().union(*(function.clocks for function in functions.values())))
        from .scoped_facts import deterministic_functions, emit_scoped_facts
        deterministic = deterministic_functions(lowered)
        certificate = ""
        if randomized and deterministic:
            from types import SimpleNamespace
            unit = SimpleNamespace(deterministic_functions=deterministic, lowered=lowered, imports={},
                namespace="«%s»" % namespace if namespace else "", lean_module=module, real_semantics=real_support)
            certificate = "\n".join(line for line in emit_scoped_facts(unit).splitlines()
                                    if not line.startswith("import "))
        metadata = [{"name": function.name,
                     "display_name": (function.class_name + "." + function.method_name) if function.class_name else function.name,
                     "lean_input_type": public_types(function)[0],
                     "lean_output_type": public_types(function)[1],
                     "parameters": [{"name": name, "type": typ} for name, typ in function.parameters],
                     "return_type": function.return_type,
                     "clocks": clocks,
                     **interface_metadata(function, bool(clocks), randomized=function.name not in deterministic, probability=randomized, parallel=function.name in parallel_admitted),
                     "points": list(function.points.values())} for function in functions.values()]
        stats = {"program_lines": len(program_lean.splitlines()),
                 "shared_lines": len(shared_lean.splitlines()),
                 "general_lines": len(lean.splitlines()),
                 "points_lines": len(points_lean.splitlines()),
                 "total_lines": len(lean.splitlines()) + len(points_lean.splitlines())}
        probability_lean = credit_generated(emit_probability(lowered, module,
            "«%s»" % namespace if namespace else "", deterministic_functions=deterministic,
            mixed=True, determinism_certificate=certificate)) if randomized else ""
        if randomized:
            stats["probability_lines"] = len(probability_lean.splitlines())
        return CompilationResult(lean, metadata, program_lean, shared_lean, stats,
                                 module, module + "Points", points_lean, namespace,
                                 randomized, module + "Probability" if randomized else "", probability_lean)
    except SyntaxError as error:
        raise CompileError(error.msg, error.lineno or 1, error.offset or 1) from None
    except (RecursionError, MemoryError):
        raise CompileError("Program nesting or size exceeds the compiler's resource limit.") from None
