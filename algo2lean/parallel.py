"""Deterministic structured fork-join descriptions over the existing lowering.

The ordinary transition relation is a serialization. ParallelCall additionally
checks sibling memory independence and carries work and span from that same
execution. Unsupported storage/probability/module features fail explicitly.
"""
import ast

from .frontend import fail
from .source_types import tuple_elements
from .objects import sequence_descriptor


# Deliberately narrow: rows contain ordinary integer sequences. Other typed
# collection operations need their own access descriptions before admission.
NESTED_SEQUENCE = "Seq[Seq]"
NESTED_DESCRIPTOR = sequence_descriptor(NESTED_SEQUENCE)
from .emitter import (constructor, frame, state_value, changed, valid_value,
                      input_values, tuple_type, lean_type)


def _supported(function):
    def supported(typ):
        elements = tuple_elements(typ)
        return all(map(supported, elements)) if elements is not None else typ in {"Int", "Bool", "Seq", NESTED_SEQUENCE, "None"}
    return all(supported(typ) for typ in
               [function.return_type, *function.variables.values(), *function.expression_types.values()])


def parallel_functions(lowered, imports=None):
    """Select the supported deterministic call graph, including imported evidence."""
    imports = imports or {}
    safe = {name for name, lowerer in lowered.items() if _supported(lowerer.function)
            and not any(node.kind == "random" for node in lowerer.nodes)}
    while True:
        remaining = {name for name in safe if all(
            node.data[0] in safe if node.data[0] in lowered else
            getattr(imports[node.data[0]], "parallel_supported", False)
            for node in lowered[name].nodes if node.kind == "call")}
        if remaining == safe:
            return safe
        safe = remaining


def validate_parallel(functions):
    # Detailed reachability checks run after lowering. Unrelated functions may
    # use randomness or storage that does not yet have parallel access rules.
    return any(getattr(node, "fork_join", False) for function in functions.values()
               for node in ast.walk(function.node))


def require_parallel(lowered, admitted):
    for name, lowerer in lowered.items():
        if lowerer.forks and name not in admitted:
            fail(lowerer.function.node, "fork_join currently supports deterministic callees with parallel access contracts and types Int, Bool, Seq, Seq[Seq], None, and tuples. Randomized parallel execution, abstract interfaces, classes, other typed collections, and Real are not supported.")


def _term(text, start):
    while start < len(text) and text[start].isspace():
        start += 1
    if start >= len(text):
        raise AssertionError("Missing generated Lean application argument")
    if text[start] == "(":
        depth, end = 1, start + 1
        while depth:
            depth += (text[end] == "(") - (text[end] == ")")
            end += 1
        # Tuple projections remain part of the application argument, e.g.
        # `(s.v0).1` and `((s.v1).2).1`. Stopping at `)` would split a
        # well-typed sequence reference from its projection.
        while end < len(text) and text[end] == ".":
            end += 1
            while end < len(text) and (text[end].isalnum() or text[end] == "_"):
                end += 1
        return text[start:end], end
    end = start
    while end < len(text) and not text[end].isspace() and text[end] != ")":
        end += 1
    return text[start:end], end


def _strings(value):
    if isinstance(value, str):
        yield value
    elif isinstance(value, (list, tuple)):
        for item in value:
            yield from _strings(item)


def read_access(data):
    """Conservative cell reads of emitted, side-effect-free Lean expressions.

    Only compiler-produced terms are scanned. Nested sequence reads are each
    included; conditional/short-circuit expressions may conservatively include
    unchosen reads. This can reject a fork but can never hide a conflict.
    """
    reads = []
    for text in _strings(data):
        for prefix, record in (
                ("(h.read ", "Algo2LeanParallel.Access.readSeq %s %s"),
                ("(" + NESTED_DESCRIPTOR + ".get h ",
                 "Algo2LeanParallel.Access.read (.collection %s %s)")):
            start = 0
            while (start := text.find(prefix, start)) >= 0:
                ref, end = _term(text, start + len(prefix))
                index, _ = _term(text, end)
                reads.append("(" + record % (ref, index) + ")")
                start += len(prefix)
    return access_union(*dict.fromkeys(reads))


def access_union(*items):
    parts = [part for part in items if part != "Algo2LeanParallel.Access.empty"]
    if not parts:
        return "Algo2LeanParallel.Access.empty"
    result = parts[-1]
    for part in reversed(parts[:-1]):
        result = "(Algo2LeanParallel.Access.union %s %s)" % (part, result)
    return result


def _continuation(lowerer, lowered, callee_name, target, following):
    callee = lowered[callee_name]
    state = changed(target, lowerer.convert("value", callee.function.return_type, lowerer.field_types[target]))
    result = "fun result => match result with | .%s value => %s" % (constructor(callee_name), frame(lowerer, following, state))
    if len(lowered) > 1:
        result += " | _ => .invalid"
    return "(" + result + ")"


def action(lowerer, lowered, pc, node, imports=None):
    imports = imports or {}
    guard = None
    access = read_access(node.data)
    if pc in lowerer.forks:
        rightpc, following = lowerer.forks[pc]
        left_name, left_args, left_target, _, _ = node.data
        right_name, right_args, right_target, _, _ = lowerer.nodes[rightpc].data
        left, right = lowered[left_name], lowered[right_name]
        left_frame = frame(left, left.entry, state_value(left, left_args))
        right_frame = frame(right, right.entry, state_value(right, right_args))
        state = "{ s with %s := leftValue, %s := rightValue }" % (left_target, right_target)
        continuation = "(fun leftResult rightResult => match leftResult, rightResult with | .%s leftValue, .%s rightValue => %s" % (
            constructor(left_name), constructor(right_name), frame(lowerer, following, state))
        if len(lowered) > 1:
            continuation += " | _, _ => .invalid"
        continuation += ")"
        return ".fork %s %s %s" % (left_frame, right_frame, continuation)
    if node.kind == "stuck":
        return ".fail"
    if node.kind == "return":
        guard = valid_value(lowerer.function.return_type, node.data)
        result = ".ret (Result.%s (%s)) %s" % (constructor(lowerer.function.name), node.data, access)
    elif node.kind == "assign":
        target, value, following, guard = node.data
        result = ".step h %s %s" % (frame(lowerer, following, changed(target, value)), access)
    elif node.kind == "allocate":
        target, contents, following, guard = node.data
        # Copying a sequence reads its entire mathematical contents. Allocation
        # already forbids this action in every fork child.
        extra = "Algo2LeanParallel.Access.allocation"
        if contents.startswith("(h.store "):
            ref, _ = _term(contents, len("(h.store "))
            extra = "(Algo2LeanParallel.Access.union %s { reads := fun x => ∃ i, x = .seq %s i, writes := fun _ => False, allocates := false })" % (extra, ref)
        result = ".step (h.allocate %s) %s %s" % (contents,
            frame(lowerer, following, changed(target, "h.nextRef")), access_union(access, extra))
    elif node.kind == "sequence_allocate":
        target, allocation, following, guard = node.data
        extra = "Algo2LeanParallel.Access.allocation"
        copy_prefix = "(" + NESTED_DESCRIPTOR + ".copy h "
        if allocation.startswith(copy_prefix):
            ref, _ = _term(allocation, len(copy_prefix))
            extra = "(Algo2LeanParallel.Access.union %s { reads := fun x => ∃ i, x = .collection %s i, writes := fun _ => False, allocates := false })" % (extra, ref)
        result = ".step %s.1 %s %s" % (allocation,
            frame(lowerer, following, changed(target, "h.nextCollection")), access_union(access, extra))
    elif node.kind == "sequence_write":
        sequence_type, data = node.data
        assert sequence_type == NESTED_SEQUENCE
        ref, index, value, target, following, expression_guard = data
        descriptor = sequence_descriptor(sequence_type)
        from .compiler import all_guards
        guard = all_guards(expression_guard, "%s.valid h %s" % (descriptor, ref))
        access = access_union(access, "(Algo2LeanParallel.Access.write (.collection %s %s))" % (ref, index))
        result = ".step (%s.set h %s %s %s) %s %s" % (descriptor, ref, index, value,
            frame(lowerer, following, changed(target, ref) if target else "s"), access)
    elif node.kind == "write":
        ref, index, value, target, following, expression_guard = node.data
        guard = "%s < h.nextRef" % ref
        if expression_guard:
            guard = "(%s) ∧ (%s)" % (expression_guard, guard)
        access = access_union(access, "(Algo2LeanParallel.Access.writeSeq %s %s)" % (ref, index))
        result = ".step (h.write %s %s %s) %s %s" % (ref, index, value,
            frame(lowerer, following, changed(target, ref) if target else "s"), access)
    elif node.kind == "noop":
        result = ".step h %s %s" % (frame(lowerer, node.data), access)
    elif node.kind == "tick":
        clock, amount, following, guard = node.data
        result = '.step (h.tick "%s" %s) %s %s' % (clock, amount, frame(lowerer, following), access)
    elif node.kind == "branch":
        condition, yes, no = node.data
        result = "if %s then .step h %s %s else .step h %s %s" % (
            condition, frame(lowerer, yes), access, frame(lowerer, no), access)
    elif node.kind == "call":
        name, args, target, following, guard = node.data
        if name in imports:
            call = imports[name]
            from .emitter import tuple_value
            continuation = imported_continuation(lowerer, call, target, following)
            result = ".invoke (Algo2LeanParallel.Eval.invocation %s h (%s %s) %s)" % (
                call.source("parallelNext"), call.entry, tuple_value(args), continuation)
        else:
            callee = lowered[name]
            result = ".call %s %s" % (frame(callee, callee.entry, state_value(callee, args)),
                _continuation(lowerer, lowered, name, target, following))
    else:
        raise AssertionError("Unsupported parallel instruction: " + node.kind)
    return "if %s then %s else .fail" % (guard, result) if guard else result


def imported_continuation(lowerer, call, target, following):
    state = changed(target, lowerer.convert("result", call.function.return_type, lowerer.field_types[target]))
    text = "fun value => match value with | .%s result => %s" % (constructor(call.name), frame(lowerer, following, state))
    if call.result_count > 1:
        text += " | _ => .invalid"
    return "(" + text + ")"


def emit_parallel(lines, lowered, namespace, imports=None, admitted=None):
    imports = imports or {}
    admitted = parallel_functions(lowered, imports) if admitted is None else admitted
    require_parallel(lowered, admitted)
    lines += ["", "namespace Algo2LeanGenerated", "",
        "-- Structured fork-join costs and access checks for the same lowered source.",
        "def parallelNext (h : Heap) : Frame → Algo2LeanParallel.Action Heap Frame Result",
        "  | .invalid => .fail"]
    for lowerer in lowered.values():
        if lowerer.function.name not in admitted:
            lines.append("  | .%s _ _ => .fail" % constructor(lowerer.function.name))
            continue
        lines.append("  | .%s pc s => match pc with" % constructor(lowerer.function.name))
        for pc, node in enumerate(lowerer.nodes):
            lines.append("    | %d => %s" % (pc, action(lowerer, lowered, pc, node, imports)))
        lines.append("    | _ => .fail")
    for key in dict.fromkeys(call.frame for call in imports.values()):
        lines.append("  | .%s _ _ _ => .fail" % key)
    lines += ["", "end Algo2LeanGenerated", ""]
    from .public_names import function_namespace, function_reference
    for lowerer in lowered.values():
        function = lowerer.function
        if function.name not in admitted or getattr(function.node, "parallel_adapter", False):
            continue
        name = function_namespace(function)
        initial = frame(lowerer, lowerer.entry, state_value(lowerer, input_values(function.parameters)))
        valid = function_reference(function, "ValidInput", namespace, False)
        lines += ["/-- Completed race-free structured execution with costs and access bounds.",
            "The ordinary Call relation describes its sequential serialization. -/",
            "def %s.ParallelCall (h : Heap) (input : %s) (finalHeap : Heap) (output : %s)" % (
                name, tuple_type(function.parameters), lean_type(function.return_type)),
            "    (cost : Algo2LeanParallel.Cost) (access : Algo2LeanParallel.Access) : Prop :=",
            "  %s h input ∧ Algo2LeanParallel.Eval parallelNext h %s finalHeap (Result.%s output) cost access" % (
                valid, initial, constructor(function.name)), ""]

    from .parallel_simulation import emit_simulation
    emit_simulation(lines, lowered, namespace, imports, admitted)
