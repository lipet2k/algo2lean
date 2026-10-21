"""Checked serialization bridges for generated structured fork-join programs."""

from .emitter import constructor
from .probability import _rules


def _step(tag, guard, indent):
    premise = " (by assumption)" if guard else ""
    return [indent + "intro final result rest stack",
            indent + "exact (Algo2LeanCore.Reaches.single (Step.%s h s stack%s)).trans (rest stack)" % (tag, premise)]


def _call(tag, guard, indent):
    premise = " (by assumption)" if guard else ""
    return [indent + "intro middle value final result first rest stack",
            indent + "apply Algo2LeanCore.Reaches.prepend (Step.%s h s stack%s)" % (tag, premise),
            indent + "exact (first _).trans (by cases value <;> simpa only [Algo2LeanCore.resumeConfig] using rest stack)"]


def _fork(lowerer, lowered, pc, indent):
    rightpc, _ = lowerer.forks[pc]
    left_name, _, left_target, _, _ = lowerer.nodes[pc].data
    right_name = lowerer.nodes[rightpc].data[0]
    name = lowerer.function.name
    lines = [indent + "intro middle leftValue joined rightValue final result first second rest",
             indent + "cases leftValue with"]
    for left in lowered:
        lines.append(indent + "| %s leftValue =>" % constructor(left))
        if left != left_name:
            lines.append(indent + "  exact False.elim (parallel_invalid_summary rest)")
            continue
        lines.append(indent + "  cases rightValue with")
        for right in lowered:
            lines.append(indent + "  | %s rightValue =>" % constructor(right))
            body = indent + "    "
            if left != left_name or right != right_name:
                lines.append(body + "exact False.elim (parallel_invalid_summary rest)")
                continue
            lines.extend([
                body + "intro stack",
                body + "apply Algo2LeanCore.Reaches.prepend (Step.%s_pc%d h s stack)" % (name, pc),
                body + "apply Algo2LeanCore.Reaches.trans (first _)",
                body + "apply Algo2LeanCore.Reaches.prepend (Step.%s_pc%d middle { s with %s := leftValue } stack)" % (name, rightpc, left_target),
                body + "exact (second _).trans (by simpa only [Algo2LeanCore.resumeConfig] using rest stack)",
            ])
    return lines


def emit_simulation(lines, lowered, namespace, imports=None, admitted=None):
    """Append a one-instruction certificate and source-facing Call projections."""
    imports = imports or {}
    admitted = set(lowered) if admitted is None else admitted
    lines.extend([
        "", "namespace Algo2LeanGenerated", "",
        "private theorem parallel_invalid_summary {h final : Heap} {result : Result} :",
        "    ¬ Algo2LeanCore.Summary Step h Frame.invalid final result := by",
        "  apply Algo2LeanParallel.not_summary_of_stuck",
        "  intro after transition",
        "  cases transition", "",
        "private theorem parallelNext_simulates (h : Heap) (f : Frame) :",
        "    Algo2LeanParallel.Action.Simulates Step h f (parallelNext h f) := by",
        "  cases f with",
        "  | invalid => trivial",
    ])
    for name, lowerer in lowered.items():
        if name not in admitted:
            lines.append("  | %s pc s => trivial" % constructor(name))
            continue
        rules = _rules(lowerer, lowered, imports)
        lines.extend([
            "  | %s pc s =>" % constructor(name),
            "      simp only [parallelNext]",
            "      split",
        ])
        for pc, node in enumerate(lowerer.nodes):
            tag = "%s_pc%d" % (name, pc)
            if node.kind == "stuck":
                lines.append("      · trivial")
            elif pc in lowerer.forks:
                code = _fork(lowerer, lowered, pc, "        ")
                lines.append("      · " + code[0].lstrip())
                lines.extend(code[1:])
            elif node.kind == "branch":
                lines.append("      · split")
                for suffix in ("true", "false"):
                    code = _step(tag + "_" + suffix, True, "          ")
                    # The false Boolean branch provides a negated equality.
                    if suffix == "false":
                        code[1] = code[1].replace("(by assumption)", "(by simpa using (by assumption : ¬ %s = true))" % node.data[0])
                    lines.append("        · " + code[0].lstrip())
                    lines.extend(code[1:])
            else:
                guard = rules[tag][1]
                indent = "          " if guard else "        "
                if node.kind == "return":
                    premise = " (by assumption)" if guard else ""
                    code = [indent + "intro stack",
                            indent + "exact Algo2LeanCore.Reaches.single (Step.%s h s stack%s)" % (tag, premise)]
                elif node.kind == "call":
                    callee = node.data[0]
                    if callee in imports:
                        call = imports[callee]
                        premise = " (by assumption)" if guard else ""
                        code = [indent + "intro middle following cost access final result first rest stack",
                                indent + "apply Algo2LeanCore.Reaches.prepend (Step.%s h s stack%s)" % (tag, premise),
                                indent + "exact (Algo2LeanParallel.invocation_summary %s %s_simulates first stack).trans (rest stack)" % (call.source("parallelSimulation"), call.frame)]
                    else:
                        code = _call(tag, guard, indent)
                else:
                    code = _step(tag, guard, indent)
                if guard:
                    lines.append("      · split")
                    lines.append("        · " + code[0].lstrip())
                    lines.extend(code[1:])
                    lines.append("        · trivial")
                else:
                    lines.append("      · " + code[0].lstrip())
                    lines.extend(code[1:])
        lines.append("      · trivial")
    for key in dict.fromkeys(call.frame for call in imports.values()):
        lines.append("  | %s frame inner resume => trivial" % key)
    lines.extend([
        "", "/-- Every structured parallel execution has its ordinary source serialization. -/",
        "theorem parallelSimulation : Algo2LeanParallel.Simulation parallelNext Step :=",
        "  Algo2LeanParallel.Simulation.of_simulates parallelNext_simulates",
        "", "end Algo2LeanGenerated", "",
    ])
    from .public_names import function_namespace, function_reference
    for lowerer in lowered.values():
        function = lowerer.function
        if function.name not in admitted or getattr(function.node, "parallel_adapter", False):
            continue
        name = function_namespace(function)
        parallel = function_reference(function, "ParallelCall", namespace, False)
        call = function_reference(function, "Call", namespace, False)
        lines.extend([
            "/-- Reuse ordinary correctness and mutation contracts for this same execution. -/",
            "theorem %s.ParallelCall.call {before input after output cost access}" % name,
            "    (run : %s before input after output cost access) :" % parallel,
            "    %s before input after output :=" % call,
            "  ⟨run.1, run.2.summary parallelSimulation⟩", "",
        ])
