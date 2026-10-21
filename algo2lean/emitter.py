"""Emit a direct transition relation and transcript-derived output views."""

from .objects import (raw_type, default_value, emit_classes, emit_collections,
                      collection_types, collection_descriptor, sequence_descriptor, tuple_projection, uses_reals)
from .source_types import contains_reference, is_collection, is_sequence, sequence_element, tuple_elements


def constructor(name):
    return "fn_%s" % name


def lean_type(typ, values=False):
    return "Seq" if values and typ == "Seq" else raw_type(typ)


def object_type(typ):
    # A bare integer sequence retains its existing ordinary-value public view.
    # References nested in value types must keep their identity and explicit heap.
    return typ != "Seq" and contains_reference(typ)


def input_needs_heap(function):
    return any(object_type(typ) for _, typ in function.parameters)


def public_types(function):
    inputs = tuple_type(function.parameters, not input_needs_heap(function))
    if input_needs_heap(function):
        inputs = "Heap × (%s)" % inputs
    output = lean_type(function.return_type, True)
    if object_type(function.return_type):
        output = "Heap × (%s)" % output
    return inputs, output


def valid_value(typ, value, heap="h"):
    elements = tuple_elements(typ)
    if elements is not None:
        from .compiler import all_guards
        return all_guards(*(valid_value(element, tuple_projection(value, i, len(elements)), heap)
                            for i, element in enumerate(elements)))
    if typ == "Seq":
        return "%s < %s.nextRef" % (value, heap)
    if is_collection(typ):
        return "%s.valid %s %s" % (collection_descriptor(typ), heap, value)
    if object_type(typ):
        if typ.endswith("?"):
            return "(∀ ref ∈ %s, is_%s %s ref)" % (value, typ[:-1], heap)
        return "is_%s %s %s" % (typ, heap, value)
    return None


def tuple_type(parameters, values=False):
    return " × ".join(lean_type(typ, values) for _, typ in parameters) or "Unit"


def input_values(parameters, name="input"):
    if len(parameters) <= 1:
        return [name] if parameters else []
    return [name + ".2" * i + (".1" if i < len(parameters) - 1 else "")
            for i in range(len(parameters))]


def tuple_value(values):
    return "()" if not values else values[0] if len(values) == 1 else "(%s)" % ", ".join(values)


def state_value(lowerer, args):
    assignments = ["%s := %s" % (lowerer.fields[name], value)
                   for (name, _), value in zip(lowerer.function.parameters, args)]
    return "({ %s } : State_%s)" % (", ".join(assignments), lowerer.function.name)


def frame(lowerer, pc, state="s"):
    return "(Frame.%s %s %s)" % (constructor(lowerer.function.name), pc, state)


def active(lowerer, pc, heap="h", state="s", stack="stack"):
    return "(.active %s %s %s)" % (heap, frame(lowerer, pc, state), stack)


def changed(target, value):
    return "{ s with %s := %s }" % (target, value)


def emit_step(lines, lowerer, lowered, imports=None):
    name = lowerer.function.name
    typ = lean_type(lowerer.function.return_type)
    for pc, node in enumerate(lowerer.nodes):
        if node.kind == "stuck":
            continue
        context = "(h : Heap) (s : State_%s) (stack : Stack)" % name
        before = active(lowerer, pc)
        tag = "%s_pc%d" % (name, pc)
        guard = None
        if node.kind == "return":
            guard = valid_value(lowerer.function.return_type, node.data)
            after = "(Algo2LeanCore.resumeConfig h (Result.%s (%s)) stack)" % (constructor(name), node.data)
        elif node.kind == "assign":
            target, value, following, guard = node.data
            after = active(lowerer, following, state=changed(target, value))
        elif node.kind == "random":
            target, lower, upper, following = node.data
            context += " (value : Int) (lowerBound : %s ≤ value) (upperBound : value < %s)" % (lower, upper)
            after = active(lowerer, following, state=changed(target, "value"))
        elif node.kind == "allocate":
            target, contents, following, guard = node.data
            after = active(lowerer, following, "(h.allocate %s)" % contents, changed(target, "h.nextRef"))
        elif node.kind == "write":
            ref, index, value, target, following, expression_guard = node.data
            guard = "%s < h.nextRef" % ref
            if expression_guard:
                guard = "(%s) ∧ (%s)" % (expression_guard, guard)
            after = active(lowerer, following, "(h.write %s %s %s)" % (ref, index, value), changed(target, ref) if target else "s")
        elif node.kind == "sequence_allocate":
            target, allocation, following, guard = node.data
            after = active(lowerer, following, allocation + ".1",
                           changed(target, "h.nextCollection"))
        elif node.kind == "heap_update":
            heap, target, value, following, guard = node.data
            after = active(lowerer, following, heap, changed(target, value) if target else "s")
        elif node.kind == "sequence_write":
            sequence_type, data = node.data
            ref, index, value, target, following, expression_guard = data
            descriptor = sequence_descriptor(sequence_type)
            from .compiler import all_guards
            guard = all_guards(expression_guard, "%s.valid h %s" % (descriptor, ref))
            after = active(lowerer, following, "(%s.set h %s %s %s)" % (descriptor, ref, index, value),
                           changed(target, ref) if target else "s")
        elif node.kind == "object_allocate":
            cls, target, following = node.data
            class_tag = lowerer.function.classes[cls].runtime_tag or cls
            after = active(lowerer, following, '(h.allocateObject "%s")' % class_tag,
                           changed(target, lowerer.convert("h.nextObject", cls, lowerer.field_types[target])))
        elif node.kind == "field_write":
            cls, field_name, ref, value, following, guard = node.data
            from .compiler import all_guards
            guard = all_guards(guard, "is_%s h (%s)" % (cls, ref))
            after = active(lowerer, following, "(set_%s_%s h (%s) (%s))" % (cls, field_name, ref, value))
        elif node.kind == "noop":
            after = active(lowerer, node.data)
        elif node.kind == "tick":
            clock_name, amount, following, guard = node.data
            after = active(lowerer, following, '(h.tick "%s" %s)' % (clock_name, amount))
        elif node.kind == "branch":
            condition, yes, no = node.data
            for suffix, truth, following in [("true", "true", yes), ("false", "false", no)]:
                lines.extend([
                    "  | %s_%s %s (condition : %s = %s) :" % (tag, suffix, context, condition, truth),
                    "      Step %s %s" % (before, active(lowerer, following)),
                ])
            continue
        elif node.kind == "call":
            callee_name, args, target, following, guard = node.data
            if imports and callee_name in imports:
                imported = imports[callee_name]
                original = imported.name
                continuation = "fun value => match value with | .%s result => %s | _ => .invalid" % (
                    constructor(original), frame(lowerer, following, changed(target,
                        lowerer.convert("result", imported.function.return_type, lowerer.field_types[target]))))
                # A one-result module needs no catch-all (Lean rejects redundant patterns).
                if imported.result_count == 1:
                    continuation = continuation.removesuffix(" | _ => .invalid")
                after = "(.active h (Frame.%s (%s %s) [] (%s)) stack)" % (
                    imported.frame, imported.entry, tuple_value(args), continuation)
                premise = " (defined : %s)" % guard if guard else ""
                lines.extend(["  | %s %s%s :" % (tag, context, premise),
                              "      Step %s %s" % (before, after)])
                continue
            callee = lowered[callee_name]
            continuation = "fun value => match value with | .%s result => %s" % (
                constructor(callee_name), frame(lowerer, following, changed(target,
                    lowerer.convert("result", callee.function.return_type, lowerer.field_types[target]))))
            if len(lowered) > 1:
                continuation += " | _ => .invalid"
            after = active(callee, callee.entry, state=state_value(callee, args), stack="((%s) :: stack)" % continuation)
        else:
            raise AssertionError("Unknown instruction: " + node.kind)
        premise = " (defined : %s)" % guard if guard else ""
        lines.extend([
            "  | %s %s%s :" % (tag, context, premise),
            "      Step %s %s" % (before, after),
        ])


def emit_public(lines, lowerer, has_clocks=False, namespace="", dependencies=False):
    from .public_names import function_namespace, function_reference
    function = lowerer.function
    name = function_namespace(function)
    reference = lambda member: function_reference(function, member, namespace, dependencies)
    args = input_values(function.parameters)
    raw_input = tuple_type(function.parameters)
    raw_output = lean_type(function.return_type)
    value_input, value_output = public_types(function)
    initial_frame = frame(lowerer, lowerer.entry, state_value(lowerer, args))
    validity = " ∧ ".join(guard for (_, typ), value in zip(function.parameters, args)
                          if (guard := valid_value(typ, value))) or "True"
    lines.extend([
        "def %s.ValidInput (%s : Heap) (%s : %s) : Prop := %s" % (name, "h" if validity != "True" else "_h", "input" if validity != "True" else "_input", raw_input, validity),
        "def %s.initial (h : Heap) (%s : %s) : Configuration :=" % (name, "input" if args else "_input", raw_input),
        "  Algo2LeanCore.start h %s" % initial_frame,
        "def %s.Run (h : Heap) (input : %s) (h' : Heap) (output : %s) : Prop :=" % (name, raw_input, raw_output),
        "  %s h input ∧ Algo2LeanCore.Reaches Step (%s h input) (.done h' (Result.%s output))" % (reference("ValidInput"), reference("initial"), constructor(function.name)),
        "def %s.ValidHeapTranscript (h : Heap) (input : %s) (trace : Transcript) : Prop :=" % (name, raw_input),
        "  %s h input ∧ ∃ final, Algo2LeanCore.Valid Step (%s h input) trace final" % (reference("ValidInput"), reference("initial")),
        "def %s.Call (h : Heap) (input : %s) (h' : Heap) (output : %s) : Prop :=" % (name, raw_input, raw_output),
        "  %s h input ∧ Algo2LeanCore.Summary Step h %s h' (Result.%s output)" % (reference("ValidInput"), initial_frame, constructor(function.name)),
        "-- Complete this function from the supplied local state, under any caller stack.",
        "def %s.CallFrom (state : Configuration) (finalHeap : Heap) (output : %s) : Prop :=" % (name, raw_output),
        "  match state with",
        "  | .active heap (Frame.%s pc locals) _ =>" % constructor(function.name),
        "      Algo2LeanCore.Summary Step heap (Frame.%s pc locals) finalHeap (Result.%s output)" % (constructor(function.name), constructor(function.name)),
        "  | _ => False",
    ])
    if input_needs_heap(function):
        lines.extend([
            "-- Object inputs carry their heap, preserving shared references and cycles.",
            "def %s.load (input : %s) : Heap × (%s) := input" % (name, value_input, raw_input),
        ])
    else:
        lines.extend([
            "-- The value view gives each sequence input its own object.",
            "def %s.load (%s : %s) : Heap × (%s) :=" % (name, "input" if args else "_input", value_input, raw_input),
            "  let h0 : Heap := {}",
        ])
    raw_values = []
    heap_index = 0
    for (_, typ), value in ([] if input_needs_heap(function) else zip(function.parameters, args)):
        if typ == "Seq":
            lines.append("  let h%d := h%d.allocate %s" % (heap_index + 1, heap_index, value))
            raw_values.append("(%d : SeqRef)" % heap_index)
            heap_index += 1
        else:
            raw_values.append(value)
    if not input_needs_heap(function):
        lines.append("  (h%d, %s)" % (heap_index, tuple_value(raw_values)))
    lines.extend([
        "def %s.ValidTranscript (my_input : %s) (trace : Transcript) : Prop :=" % (name, value_input),
        "  let loaded := %s my_input" % reference("load"),
        "  %s loaded.1 loaded.2 trace" % reference("ValidHeapTranscript"),
        "def %s.Returns (my_input : %s) (my_output : %s) : Prop :=" % (name, value_input, value_output),
        "  let loaded := %s my_input" % reference("load"),
    ])
    if function.return_type == "Seq":
        lines.append("  ∃ finalHeap result, %s loaded.1 loaded.2 finalHeap result ∧ finalHeap.store result = my_output" % reference("Run"))
    elif object_type(function.return_type):
        lines.append("  %s loaded.1 loaded.2 my_output.1 my_output.2" % reference("Run"))
    else:
        lines.append("  ∃ finalHeap, %s loaded.1 loaded.2 finalHeap my_output" % reference("Run"))
    lines.append("")
    if has_clocks:
        emit_cost_interface(lines, function, value_input, value_output, namespace, dependencies)
    parameter = " {dependencies : Dependencies}" if dependencies else ""
    lines.extend([
        "theorem %s.Call.run%s {before input after output}" % (name, parameter),
        "    (call : %s before input after output) :" % reference("Call"),
        "    %s before input after output :=" % reference("Run"),
        "  ⟨call.1, call.2.root⟩", "",
    ])


def emit_cost_interface(lines, function, value_input, value_output, namespace="", dependencies=False):
    """Emit the relation connecting outputs and clock increments of one execution."""
    from .public_names import function_namespace, function_reference
    name = function_namespace(function)
    reference = lambda member: function_reference(function, member, namespace, dependencies)
    lines.extend([
        "-- Output and clock increments from one completed execution.",
        "def %s.ReturnsWithCost (my_input : %s) (my_output : %s) (costs : Clocks) : Prop :=" % (name, value_input, value_output),
        "  let loaded := %s my_input" % reference("load"),
    ])
    if function.return_type == "Seq":
        lines.append("  ∃ finalHeap result, %s loaded.1 loaded.2 finalHeap result ∧ finalHeap.store result = my_output ∧ Heap.cost loaded.1 finalHeap = costs" % reference("Run"))
        extract, project = "⟨heap, result, execution, value, _⟩", "⟨heap, result, execution, value⟩"
        restore, witness = "⟨heap, result, execution, value⟩", "⟨Heap.cost (%s input).1 heap, heap, result, execution, value, rfl⟩" % reference("load")
    elif object_type(function.return_type):
        lines.append("  %s loaded.1 loaded.2 my_output.1 my_output.2 ∧ Heap.cost loaded.1 my_output.1 = costs" % reference("Run"))
        extract, project = "⟨execution, _⟩", "execution"
        restore, witness = None, "⟨Heap.cost (%s input).1 output.1, run, rfl⟩" % reference("load")
    else:
        lines.append("  ∃ finalHeap, %s loaded.1 loaded.2 finalHeap my_output ∧ Heap.cost loaded.1 finalHeap = costs" % reference("Run"))
        extract, project = "⟨heap, execution, _⟩", "⟨heap, execution⟩"
        restore, witness = "⟨heap, execution⟩", "⟨Heap.cost (%s input).1 heap, heap, execution, rfl⟩" % reference("load")
    parameter = " {dependencies : Dependencies}" if dependencies else ""
    lines.extend([
        "theorem %s.ReturnsWithCost.returns%s {input output costs}" % (name, parameter),
        "    (run : %s input output costs) : %s input output := by" % (reference("ReturnsWithCost"), reference("Returns")),
        "  obtain %s := run" % extract,
        "  exact %s" % project,
        "theorem %s.Returns.withCost%s {input output}" % (name, parameter),
        "    (run : %s input output) : ∃ costs, %s input output costs := by" % (reference("Returns"), reference("ReturnsWithCost")),
    ])
    if restore is not None:
        lines.append("  obtain %s := run" % restore)
    lines.extend(["  exact %s" % witness, ""])


def emit_points(lines, lowerer, namespace="", dependencies=False):
    from .public_names import function_namespace, function_reference, identifier
    function = lowerer.function
    public = function_namespace(function)
    variables = {}
    for node_id, point in function.points.items():
        pc = lowerer.point_pcs[node_id]
        stem = public + ".At." + identifier(point["name"])
        lines.extend([
            "-- Before source line %d, column %d; location only, not reachability." % (point["line"], point["column"]),
            "def %s : Configuration → Prop" % stem,
            "  | .active _ (.fn_%s %d _) _ => True" % (function.name, pc),
            "  | _ => False",
        ])
        for variable in point["variables"]:
            variables.setdefault(variable["name"], (variable["type"], set()))[1].add(pc)
    for name, (typ, pcs) in variables.items():
        field = lowerer.fields[name]
        lines.append("def %s.Local.%s : Configuration → Option %s" % (public, identifier(name), lean_type(typ)))
        available = " ∨ ".join("pc = %d" % pc for pc in sorted(pcs))
        lines.append("  | .active _ (.fn_%s pc s) _ => if %s then some s.%s else none" % (function.name, available, field))
        lines.append("  | _ => none")
        if typ == "Seq":
            lines.extend([
                "def %s.Element.%s (state : Configuration) (index : Int) : Option Int :=" % (public, identifier(name)),
                "  (%s state).map (fun ref => state.heap.read ref index)" % function_reference(function, "Local." + identifier(name), namespace, dependencies),
            ])
        elif is_sequence(typ):
            lines.extend([
                "def %s.Element.%s (state : Configuration) (index : Int) : Option %s :=" % (public, identifier(name), raw_type(sequence_element(typ))),
                "  (%s state).bind (fun ref => %s.get state.heap ref index)" % (function_reference(function, "Local." + identifier(name), namespace, dependencies), sequence_descriptor(typ)),
            ])
    if function.points:
        lines.append("")


def emit_program(lowered, namespace=""):
    lines = ["-- Generated direct transitions; outputs are completed valid transcripts.", "namespace Algo2LeanGenerated", ""]
    if uses_reals(lowerer.function for lowerer in lowered.values()):
        lines[0:0] = ["noncomputable section", ""]
    emit_classes(lines, next(iter(lowered.values())).function.classes)
    emit_collections(lines, collection_types(lowerer.function for lowerer in lowered.values()))
    for lowerer in lowered.values():
        lines.append("structure State_%s where" % lowerer.function.name)
        for name, typ in lowerer.field_types.items():
            representation, initial = lowerer.field_representation(name)
            lines.append("  %s : %s := %s -- %s" % (name, representation, initial, lowerer.field_labels[name]))
        if not lowerer.field_types:
            lines.append("  unused : Unit := ()")
        lines.append("")
    lines.extend(["inductive Frame where", "  | invalid"])
    for lowerer in lowered.values():
        lines.append("  | %s (pc : Nat) (state : State_%s)" % (constructor(lowerer.function.name), lowerer.function.name))
    lines.extend(["", "inductive Result where"])
    for lowerer in lowered.values():
        lines.append("  | %s (value : %s)" % (constructor(lowerer.function.name), lean_type(lowerer.function.return_type)))
    lines.extend([
        "", "abbrev Configuration := Algo2LeanCore.Config Heap Frame Result",
        "abbrev Stack := Algo2LeanCore.Stack Frame Result",
        "abbrev Transcript := List Configuration", "",
        "inductive Step : Configuration → Configuration → Prop where",
    ])
    for lowerer in lowered.values():
        emit_step(lines, lowerer, lowered)
    lines.append("")
    lines.extend(["end Algo2LeanGenerated", "", "open Algo2LeanGenerated", ""])
    has_clocks = any(lowerer.function.clocks for lowerer in lowered.values())
    for lowerer in lowered.values():
        emit_public(lines, lowerer, has_clocks, namespace)
    if any(lowerer.forks for lowerer in lowered.values()):
        from .parallel import emit_parallel
        emit_parallel(lines, lowered, namespace)
    if uses_reals(lowerer.function for lowerer in lowered.values()):
        lines.append("end")
    return "\n".join(lines) + "\n"


def emit_points_module(lowered, module, namespace=""):
    # Escaping keeps user-selected file stems importable even if a name is a
    # Lean keyword. Validation forbids paths and delimiter characters.
    lines = ["import «%s»" % module, "", "open Algo2LeanGenerated", "",
             "-- Named-line observations; changing labels leaves the imported algorithm unchanged.", ""]
    if uses_reals(lowerer.function for lowerer in lowered.values()):
        lines.insert(1, "noncomputable section")
    for lowerer in lowered.values():
        emit_points(lines, lowerer, namespace)
    if uses_reals(lowerer.function for lowerer in lowered.values()):
        lines.append("end")
    return "\n".join(lines) + "\n"
