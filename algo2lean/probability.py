"""Optional probabilistic semantics, checked against the generated transitions.

The ordinary algorithm file keeps its lightweight relational interface. This
companion describes finite choices and proves their support is exactly Step;
the shared probability library supplies execution laws and analysis tools.
"""

from .emitter import active, constructor, emit_step


def has_randomness(lowered):
    return any(node.kind == "random" for lowerer in lowered.values() for node in lowerer.nodes)


def _rules(lowerer, lowered, imports):
    """Reuse emitted successors and guards rather than reimplement instructions."""
    emitted = []
    emit_step(emitted, lowerer, lowered, imports)
    rules = {}
    for index in range(0, len(emitted), 2):
        header, body = emitted[index:index + 2]
        tag = header.split()[1]
        pc = int(tag.removeprefix(lowerer.function.name + "_pc").split("_", 1)[0])
        prefix = "      Step " + active(lowerer, pc) + " "
        if not body.startswith(prefix):
            raise AssertionError("Unexpected transition layout for " + tag)
        guard = header.split(" (defined : ", 1)[1].removesuffix(") :") if " (defined : " in header else None
        rules[tag] = (body[len(prefix):], guard)
    return rules


def emit_choices(lowered, imports=None):
    """Emit a choice description and a two-way agreement proof for concrete code.

    Imported units expose the same certificate in their own companions. Abstract
    interface code needs an additional probability contract and is handled by
    the caller before invoking this emitter.
    """
    imports = imports or {}
    dependencies = {call.frame: call for call in imports.values()}
    lines = ["namespace Algo2LeanGenerated", "", "open Algo2LeanCore", ""]
    all_rules = {}
    for name, lowerer in lowered.items():
        rules = _rules(lowerer, lowered, imports)
        all_rules[name] = rules
        lines += ["private def choice_%s (h : Heap) (s : State_%s) (stack : Stack) : Nat → Choice Configuration" % (name, name)]
        for pc, node in enumerate(lowerer.nodes):
            if node.kind == "stuck":
                continue
            tag = "%s_pc%d" % (name, pc)
            if node.kind == "branch":
                yes, no = rules[tag + "_true"][0], rules[tag + "_false"][0]
                expression = "if %s then .next %s else .next %s" % (node.data[0], yes, no)
            elif node.kind == "random":
                _, lower, upper, _ = node.data
                expression = ".uniform (%s) (%s) (fun value => %s)" % (lower, upper, rules[tag][0])
            else:
                successor, guard = rules[tag]
                expression = ".next " + successor
                if guard:
                    expression = "if %s then %s else .fail" % (guard, expression)
            lines.append("  | %d => %s" % (pc, expression))
        lines += ["  | _ => .fail", ""]

    lines += ["/-- One instruction's exact choices. Successful returns stop; invalid operations fail. -/",
              "def nextChoice : Configuration → Choice Configuration",
              "  | .done _ _ => .halt",
              "  | .active h frame stack => match frame with",
              "    | .invalid => .fail"]
    for name in lowered:
        lines.append("    | .%s pc s => choice_%s h s stack pc" % (constructor(name), name))
    for call in dependencies.values():
        lines += ["    | .%s frame inner resume =>" % call.frame,
                  "      (%s (.active h frame inner)).map (ModuleCall.config Frame.%s resume stack)" %
                  (call.source("nextChoice"), call.frame)]
    lines.append("")

    for name, lowerer in lowered.items():
        lines += ["private theorem choice_%s_context (h : Heap) (s : State_%s)" % (name, name),
                  "    (stack caller : Stack) (pc : Nat) :",
                  "    choice_%s h s (stack ++ caller) pc =" % name,
                  "      (choice_%s h s stack pc).map (CallContext.config caller) := by" % name,
                  "  unfold choice_%s" % name,
                  "  split"]
        for pc, node in enumerate(lowerer.nodes):
            if node.kind == "stuck":
                continue
            tag = "%s_pc%d" % (name, pc)
            conditional = node.kind == "branch" or all_rules[name][tag][1]
            if conditional:
                lines.append("  · split <;> simp_all [Choice.map]")
            elif node.kind == "random":
                lines.append("  · simp [Choice.map, Function.comp_def]")
            else:
                lines.append("  · simp [Choice.map]")
        lines += ["  · rfl", ""]
    lines += ["/-- The current call's choices do not depend on its suspended callers. -/",
              "theorem nextChoice_context (h : Heap) (frame : Frame) (stack caller : Stack) :",
              "    nextChoice (.active h frame (stack ++ caller)) =",
              "      (nextChoice (.active h frame stack)).map (CallContext.config caller) := by",
              "  cases frame with", "  | invalid => rfl"]
    for name in lowered:
        lines += ["  | %s pc s => exact choice_%s_context h s stack caller pc" % (constructor(name), name)]
    for call in dependencies.values():
        lines += ["  | %s frame inner resume =>" % call.frame,
                  "      simp only [nextChoice, Choice.map_map]",
                  "      congr 1",
                  "      funext state",
                  "      exact (CallContext.module_config Frame.%s resume stack caller state).symm" % call.frame]
    lines.append("")

    for name, lowerer in lowered.items():
        rules = all_rules[name]
        lines += ["private theorem choice_%s_sound (h : Heap) (s : State_%s) (stack : Stack)" % (name, name),
                  "    (pc : Nat) {after : Configuration}",
                  "    (allowed : (choice_%s h s stack pc).Allows after) :" % name,
                  "    Step (.active h (.fn_%s pc s) stack) after := by" % name,
                  "  unfold choice_%s at allowed" % name,
                  "  split at allowed"]
        for pc, node in enumerate(lowerer.nodes):
            if node.kind == "stuck":
                continue
            tag = "%s_pc%d" % (name, pc)
            if node.kind == "branch":
                lines += ["  · split at allowed", "    · cases allowed", "      exact Step.%s_true h s stack (by assumption)" % tag,
                          "    · cases allowed", "      exact Step.%s_false h s stack (by simpa using (by assumption : ¬ %s = true))" % (tag, node.data[0])]
            elif node.kind == "random":
                lines += ["  · obtain ⟨value, lowerBound, upperBound, rfl⟩ := allowed",
                          "    exact Step.%s h s stack value lowerBound upperBound" % tag]
            elif rules[tag][1]:
                lines += ["  · split at allowed", "    · cases allowed", "      exact Step.%s h s stack (by assumption)" % tag,
                          "    · exact False.elim allowed"]
            else:
                lines += ["  · cases allowed", "    exact Step.%s h s stack" % tag]
        lines += ["  · exact False.elim allowed", ""]

    lines += ["/-- The probabilistic description and transcript transitions have exactly the same support. -/",
              "theorem choice_step {before after : Configuration} :",
              "    (nextChoice before).Allows after ↔ Step before after := by",
              "  constructor", "  · intro allowed", "    cases before with",
              "    | done h result => exact False.elim allowed",
              "    | active h frame stack =>", "      cases frame with",
              "      | invalid => exact False.elim allowed"]
    for name in lowered:
        lines += ["      | %s pc s => exact choice_%s_sound h s stack pc allowed" % (constructor(name), name)]
    for call in dependencies.values():
        lines += ["      | %s frame inner resume =>" % call.frame,
                  "        obtain ⟨sourceAfter, sourceAllowed, rfl⟩ := (Choice.allows_map _ _ _).mp allowed",
                  "        exact Step.%s h frame inner resume stack sourceAfter ((%s).mp sourceAllowed)" %
                  (call.frame, call.source("choice_step"))]
    lines += ["  · intro transition", "    cases transition with"]
    for name, lowerer in lowered.items():
        rules = all_rules[name]
        for tag, (_, guard) in rules.items():
            pc = int(tag.removeprefix(name + "_pc").split("_", 1)[0])
            node = lowerer.nodes[pc]
            if node.kind == "random":
                lines += ["    | %s h s stack value lowerBound upperBound => exact ⟨value, lowerBound, upperBound, rfl⟩" % tag]
            elif node.kind == "branch":
                lines += ["    | %s h s stack condition => simp [nextChoice, choice_%s, condition, Choice.Allows]" % (tag, name)]
            elif guard:
                lines += ["    | %s h s stack defined =>" % tag, "      simp only [nextChoice, choice_%s, if_pos defined, Choice.Allows]" % name]
            else:
                lines += ["    | %s h s stack => rfl" % tag]
    for call in dependencies.values():
        lines += ["    | %s h frame inner resume stack sourceAfter transition =>" % call.frame,
                  "      exact (Choice.allows_map _ _ _).mpr ⟨sourceAfter, (%s).mpr transition, rfl⟩" % call.source("choice_step")]
    lines += ["", "end Algo2LeanGenerated", ""]
    return "\n".join(lines)


def emit_probability(lowered, module, namespace="", imports=None, facts_module="",
                     deterministic_functions=None, mixed=False, determinism_certificate=""):
    """An optional companion with source-facing execution laws and observations."""
    from .emitter import lean_type, object_type, public_types, tuple_type
    from .public_names import function_namespace, function_reference

    imports = imports or {}
    quoted = lambda name: ".".join(part if part.startswith("«") else "«%s»" % part for part in name.split("."))
    headers = ["import " + quoted(module), "import Algo2LeanLib.CallContext", "import Algo2LeanProbability.Call",
               "import Algo2LeanProbability.Observations"]
    if facts_module:
        headers += ["import " + quoted(facts_module)]
    if facts_module or determinism_certificate:
        headers += ["import Algo2LeanProbability.Deterministic"]
    headers += ["import " + quoted(name) for name in dict.fromkeys(
        call.namespace + ".Probability" for call in imports.values())]
    lines = headers + ["", "-- Optional probability semantics; checked separately with Mathlib.",
                      "noncomputable section", "attribute [local instance] Classical.propDecidable", ""]
    if determinism_certificate:
        lines += [determinism_certificate, ""]
    if namespace:
        lines += ["namespace " + namespace, "", "open _root_.Algo2LeanGenerated", ""]
    lines += [emit_choices(lowered, imports), "open Algo2LeanGenerated", ""]
    for lowerer in lowered.values():
        function = lowerer.function
        if getattr(function.node, "parallel_adapter", False):
            continue
        public = function_namespace(function)
        ref = lambda member: function_reference(function, member, namespace)
        raw_input, raw_output = tuple_type(function.parameters), lean_type(function.return_type)
        value_input, value_output = public_types(function)
        lines += [
            "/-- Successful return of this call, retaining shared storage and clock counters. -/",
            "def %s.outcome : Configuration → Option (Heap × (%s))" % (public, raw_output),
            "  | .done heap (.fn_%s result) => some (heap, result)" % function.name,
            "  | _ => none", "",
            "/-- Probability law of the whole execution. Invalid inputs enter the error state. -/",
            "def %s.law (heap : Heap) (input : %s) :" % (public, raw_input),
            "    MeasureTheory.Measure (Algo2LeanProbability.Run Configuration) := by",
            "  classical",
            "  exact Algo2LeanProbability.execution",
            "    (fun state => if %s heap input then nextChoice state else .fail)" % ref("ValidInput"),
            "    (%s heap input)" % ref("initial"), "",
            "/-- Unconditional expected reward on successful return; failed or diverging calls contribute zero. -/",
            "def %s.expectedReturn (heap : Heap) (input : %s)" % (public, raw_input),
            "    (reward : Heap → %s → ENNReal) : ENNReal := by" % raw_output,
            "  classical",
            "  exact Algo2LeanProbability.callExpected",
            "    (fun state => if %s heap input then nextChoice state else .fail)" % ref("ValidInput"),
            "    %s (%s heap input) (fun result => reward result.1 result.2)" % (ref("outcome"), ref("initial")), "",
            "/-- Expected return reward from a local state of this function, independent of its caller stack. -/",
            "def %s.expectedFrom (state : Configuration) (reward : Heap → %s → ENNReal) : ENNReal :=" % (public, raw_output),
            "  match state with",
            "  | .active heap (.fn_%s pc locals) _ =>" % function.name,
            "      Algo2LeanProbability.callExpected nextChoice %s" % ref("outcome"),
            "        (.active heap (.fn_%s pc locals) []) (fun result => reward result.1 result.2)" % function.name,
            "  | _ => 0", "",
            "/-- Reusable joint final-heap/output law, including almost-sure successful termination. -/",
            "def %s.HasLaw (heap : Heap) (input : %s) (distribution : PMF (Heap × (%s))) : Prop := by" % (public, raw_input, raw_output),
            "  classical",
            "  exact Algo2LeanProbability.HasLaw",
            "    (fun state => if %s heap input then nextChoice state else .fail)" % ref("ValidInput"),
            "    %s (%s heap input) distribution" % (ref("outcome"), ref("initial")), "",
            "/-- Unconditional probability of a successful return satisfying the joint postcondition. -/",
            "def %s.returnProbability (heap : Heap) (input : %s)" % (public, raw_input),
            "    (post : Heap → %s → Prop) : ENNReal :=" % raw_output,
            "  Algo2LeanProbability.probability (%s heap input)" % ref("law"),
            "    (Algo2LeanProbability.Event.returnsWhere %s (fun result => post result.1 result.2))" % ref("outcome"), "",
            "/-- Return events and completed-call rewards describe the same experiment. -/",
            "theorem %s.returnProbability_eq_expectedReturn (heap : Heap) (input : %s)" % (public, raw_input),
            "    (valid : %s heap input) (post : Heap → %s → Prop) :" % (ref("ValidInput"), raw_output),
            "    %s heap input post =" % ref("returnProbability"),
            "      %s heap input (fun final value => if post final value then 1 else 0) := by" % ref("expectedReturn"),
            "  classical",
            "  simp only [%s, %s, %s, if_pos valid]" % (ref("returnProbability"), ref("law"), ref("expectedReturn")),
            "  exact (Algo2LeanProbability.callProbability_eq_execution nextChoice %s" % ref("outcome"),
            "    (by intro state output seen; cases state with",
            "        | active h frame stack => simp [%s] at seen" % ref("outcome"),
            "        | done h result => rfl)",
            "    (%s heap input) (fun result => post result.1 result.2)).symm" % ref("initial"), "",
            "/-- Probability of returning this mathematical output; failure and divergence are not renormalized. -/",
            "def %s.outputProbability (input : %s) (output : %s) : ENNReal :=" % (public, value_input, value_output),
            "  let loaded := %s input" % ref("load"),
        ]
        if function.return_type == "Seq":
            predicate = "fun heap result => heap.store result = output"
        elif object_type(function.return_type):
            predicate = "fun heap result => (heap, result) = output"
        else:
            predicate = "fun _ result => result = output"
        lines += ["  %s loaded.1 loaded.2 (%s)" % (ref("returnProbability"), predicate), "",
                  "/-- Probability that this call returns successfully, without a bound on its duration. -/",
                  "def %s.terminationProbability (heap : Heap) (input : %s) : ENNReal :=" % (public, raw_input),
                  "  %s heap input (fun _ _ => True)" % ref("returnProbability"), "",
                  "/-- Total increments of a named clock, including failing and diverging paths. -/",
                  "def %s.cost (heap : Heap) (clock : String) : Algo2LeanProbability.Observable Configuration :=" % public,
                  "  Algo2LeanProbability.Observable.total (fun state => Heap.cost heap state.heap clock)", "",
                  "/-- Expected increments of a named clock over all finite prefixes, possibly infinite. -/",
                  "def %s.expectedCost (heap : Heap) (input : %s) (clock : String) : ENNReal :=" % (public, raw_input),
                  "  Algo2LeanProbability.expected (%s heap input)" % ref("law"),
                  "    (%s heap clock)" % ref("cost"), "",
                  "/-- Probability that the total clock increment exceeds a threshold, whether or not the call returns. -/",
                  "def %s.costProbability (heap : Heap) (input : %s) (clock : String) (threshold : ENNReal) : ENNReal :=" % (public, raw_input),
                  "  Algo2LeanProbability.probability (%s heap input)" % ref("law"),
                  "    (Algo2LeanProbability.Event.exceeds (%s heap clock) threshold)" % ref("cost"), ""]
        if (facts_module or determinism_certificate) and (deterministic_functions is None or function.name in deterministic_functions):
            lines += [
                "/-- Reuse a terminating deterministic call as its joint heap/output law. -/",
                "theorem %s.Call.hasLaw {before input after output}" % public,
                "    (call : %s before input after output) :" % ref("Call"),
                "    %s before input (PMF.pure (after, output)) := by" % ref("HasLaw"),
                "  simp only [%s, if_pos call.1]" % ref("HasLaw"),
                "  exact Algo2LeanProbability.HasLaw.%s nextChoice %s" % ("of_reaches_on" if mixed else "of_reaches", ref("outcome")),
                "    (fun _ _ => choice_step) " + ("deterministicRegion" if mixed else "deterministic"),
                "    (by intro state result seen; cases state with",
                "        | active h frame stack => simp [%s] at seen" % ref("outcome"),
                "        | done h result => rfl)",
                ("    (%s before input) call.2.root rfl" % ref("initial_safe") if mixed else "    call.2.root rfl"), "",
                "/-- Evaluate any joint return reward using the existing deterministic proof. -/",
                "theorem %s.Call.expectedReturn {before input after output}" % public,
                "    (call : %s before input after output)" % ref("Call"),
                "    (reward : Heap → %s → ENNReal) :" % raw_output,
                "    %s before input reward = reward after output := by" % ref("expectedReturn"),
                "  have law := %s call (fun result => reward result.1 result.2)" % ref("Call.hasLaw"),
                "  change %s before input reward =" % ref("expectedReturn"),
                "    Algo2LeanProbability.pmfExpected (PMF.pure (after, output))",
                "      (fun result => reward result.1 result.2) at law",
                "  simpa only [Algo2LeanProbability.pmfExpected_pure] using law", "",
            ]
    if namespace:
        lines += ["end " + namespace, ""]
    return "\n".join(lines)
