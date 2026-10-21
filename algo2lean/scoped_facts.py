"""One checked deterministic region per mixed execution unit.

The call graph only proposes the region. Lean checks its closure and uniqueness
against the original Step constructors, including separately compiled imports.
"""

from .emitter import constructor
from .module_facts import _qualified, _source_rules
from .public_names import function_namespace


def deterministic_functions(lowered, imports=None):
    """Greatest fixed point, retaining recursive pure functions."""
    imports = imports or {}
    safe = {name for name, lowerer in lowered.items()
            if not any(node.kind == "random" for node in lowerer.nodes)}
    while True:
        remaining = {name for name in safe if all(
            node.data[0] in safe if node.data[0] in lowered else imports[node.data[0]].deterministic
            for node in lowered[name].nodes if node.kind == "call")}
        if remaining == safe:
            return safe
        safe = remaining


def emit_scoped_facts(module):
    safe = module.deterministic_functions
    if not safe:
        return ""
    imports = {call.frame: call for call in module.imports.values()}
    admitted = {call.frame for call in module.imports.values() if call.deterministic}
    lines = ["import " + _qualified(module.lean_module), "import Algo2LeanLib.Determinism"]
    lines += ["import " + _qualified(call.namespace + ".Facts")
              for key, call in imports.items() if key in admitted]
    if module.real_semantics:
        lines += ["", "noncomputable section"]
    lines += [""] + (["namespace " + module.namespace] if module.namespace else [])
    lines += ["open Algo2LeanCore _root_.Algo2LeanGenerated", "",
              "namespace Algo2LeanGenerated", "",
              "/-- Frames whose reachable callees contain no random instruction. -/",
              "inductive SafeFrame : Frame → Prop where",
              "  | invalid : SafeFrame .invalid"]
    for name in module.lowered:
        if name in safe:
            lines += ["  | %s (pc s) : SafeFrame (.%s pc s)" % (constructor(name), constructor(name))]
    for key, call in imports.items():
        if key in admitted:
            lines += ["  | %s {frame inner resume}" % key]
            if call.mixed:
                lines += ["      (child : %s frame)" % call.source("SafeFrame"),
                          "      (inside : FrameSafety.stack %s inner)" % call.source("SafeFrame")]
            lines += ["      (continuation : ∀ result, SafeFrame (resume result)) :",
                      "      SafeFrame (.%s frame inner resume)" % key]
    lines += ["", "abbrev Safe := FrameSafety.config (Heap := Heap) (Result := Result) SafeFrame", "",
              "/-- Every actual transition stays inside the certified region. -/",
              "theorem safe_preserved {before after : Configuration}",
              "    (transition : Step before after) (safe : Safe before) : Safe after := by",
              "  cases transition with"]
    rules = {name: _source_rules(lowerer, module.lowered, module.imports)
             for name, lowerer in module.lowered.items()}
    for name, lowerer in module.lowered.items():
        for tag, (pc, _, _) in rules[name].items():
            lines += ["  | %s =>" % tag]
            if name not in safe:
                lines += ["    cases safe.1"]
                continue
            node = lowerer.nodes[pc]
            if node.kind == "return":
                lines += ["    exact FrameSafety.resume _ _ safe.2"]
            elif node.kind == "call":
                callee = node.data[0]
                lines += ["    refine ⟨?_, ?_⟩"]
                if callee in module.lowered:
                    lines += ["    · exact .%s _ _" % constructor(callee),
                              "    · apply FrameSafety.cons"]
                else:
                    call = module.imports[callee]
                    lines += ["    · apply SafeFrame.%s" % call.frame]
                    if call.mixed:
                        lines += ["      · exact .%s _ _" % constructor(call.name),
                                  "      · simp [FrameSafety.stack]"]
                    lines += ["      · intro result; cases result <;> constructor",
                              "    · exact safe.2"]
                    continue
                lines += ["      · intro result; cases result <;> constructor",
                          "      · exact safe.2"]
            else:
                lines += ["    exact ⟨.%s _ _, safe.2⟩" % constructor(name)]
    for key, call in imports.items():
        lines += ["  | %s h frame inner resume caller after transition =>" % key]
        if key not in admitted:
            lines += ["    cases safe.1"]
        elif call.mixed:
            lines += ["    obtain ⟨parent, callers⟩ := safe",
                      "    cases parent with",
                      "    | %s child inside continuation =>" % key,
                      "      have moved := %s transition ⟨child, inside⟩" % call.source("safe_preserved"),
                      "      cases after with",
                      "      | active h frame inner =>",
                      "          exact ⟨.%s moved.1 moved.2 continuation, callers⟩" % key,
                      "      | done h result => exact ⟨continuation result, callers⟩"]
        else:
            lines += ["    obtain ⟨parent, callers⟩ := safe",
                      "    cases parent with",
                      "    | %s continuation =>" % key,
                      "      cases after with",
                      "      | active h frame inner => exact ⟨.%s continuation, callers⟩" % key,
                      "      | done h result => exact ⟨continuation result, callers⟩"]
    lines += [""]
    for name, lowerer in module.lowered.items():
        if name not in safe:
            continue
        lines += ["private def next_%s (h : Heap) (s : State_%s) (stack : Stack) : Nat → Configuration" % (name, name)]
        for pc, node in enumerate(lowerer.nodes):
            if node.kind == "stuck":
                continue
            tag = "%s_pc%d" % (name, pc)
            successor = ("if %s then %s else %s" % (node.data[0], rules[name][tag + "_true"][1],
                                                   rules[name][tag + "_false"][1])
                         if node.kind == "branch" else rules[name][tag][1])
            lines += ["  | %d => %s" % (pc, successor)]
        lines += ["  | pc => .active h (.%s pc s) stack" % constructor(name), ""]
    lines += ["def next : Configuration → Configuration",
              "  | .done h result => .done h result",
              "  | .active h frame stack => match frame with",
              "    | .invalid => .active h .invalid stack"]
    for name in module.lowered:
        successor = "next_%s h s stack pc" % name if name in safe else ".active h (.%s pc s) stack" % constructor(name)
        lines += ["    | .%s pc s => %s" % (constructor(name), successor)]
    for key, call in imports.items():
        successor = ("ModuleCall.config Frame.%s resume stack (%s (.active h frame inner))" %
                     (key, call.source("next")) if key in admitted else ".active h (.%s frame inner resume) stack" % key)
        lines += ["    | .%s frame inner resume => %s" % (key, successor)]
    lines += ["", "theorem step_next_of_safe {before after : Configuration}",
              "    (transition : Step before after) (safe : Safe before) : next before = after := by",
              "  cases transition with"]
    for name in module.lowered:
        for tag, (_, _, guarded) in rules[name].items():
            if name not in safe:
                lines += ["  | %s => cases safe.1" % tag]
            elif tag.endswith(("_true", "_false")):
                lines += ["  | %s h s stack condition => simp [next, next_%s, condition]" % (tag, name)]
            else:
                lines += ["  | %s => rfl" % tag]
    for key, call in imports.items():
        lines += ["  | %s h frame inner resume caller after transition =>" % key]
        if key not in admitted:
            lines += ["    cases safe.1"]
        elif call.mixed:
            lines += ["    cases safe.1 with",
                      "    | %s child inside continuation =>" % key,
                      "      exact congrArg (ModuleCall.config Frame.%s resume caller)" % key,
                      "        (%s transition ⟨child, inside⟩)" % call.source("step_next_of_safe")]
        else:
            lines += ["    exact congrArg (ModuleCall.config Frame.%s resume caller) (%s transition)" %
                      (key, call.source("step_next"))]
    lines += ["", "theorem deterministicRegion : DeterministicOn Step Safe where",
              "  preserved := safe_preserved",
              "  unique safe first second := (step_next_of_safe first safe).symm.trans (step_next_of_safe second safe)",
              "", "end Algo2LeanGenerated", "", "open Algo2LeanGenerated", ""]
    for name, lowerer in module.lowered.items():
        if name in safe and not getattr(lowerer.function.node, "parallel_adapter", False):
            public = function_namespace(lowerer.function)
            lines += ["theorem %s.initial_safe (heap input) : Safe (%s.initial heap input) :=" % (public, public),
                      "  ⟨.%s _ _, by simp [FrameSafety.stack]⟩" % constructor(name), ""]
    return "\n".join(lines + (["end " + module.namespace] if module.namespace else []) + [""])
