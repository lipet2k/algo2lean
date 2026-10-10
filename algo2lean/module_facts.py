"""Optional, compositional determinism certificates for compiled modules.

The generated projection is a proof certificate, not an alternative execution
relation: ``step_next`` checks it against every actual transition. Imported
modules contribute their previously checked certificate once, independent of
their instruction count.
"""

from .emitter import active, constructor, emit_step


def _qualified(name):
    """Quote identifier segments without changing their Lean namespace."""
    return ".".join(part if part.startswith("«") and part.endswith("»")
                    else "«%s»" % part for part in name.split("."))


def _source_rules(lowerer, lowered, imports):
    """Read the exact emitted successors instead of maintaining a second emitter."""
    emitted = []
    emit_step(emitted, lowerer, lowered, imports)
    rules = {}
    for index in range(0, len(emitted), 2):
        header, body = emitted[index:index + 2]
        tag = header.split()[1]
        suffix = tag.removeprefix(lowerer.function.name + "_pc")
        pc = int(suffix.split("_", 1)[0])
        prefix = "      Step " + active(lowerer, pc) + " "
        if not body.startswith(prefix):
            raise AssertionError("Unexpected transition layout for " + tag)
        rules[tag] = (pc, body[len(prefix):], " (defined :" in header)
    return rules


def _source_fact(imported, name):
    """Use the original module or supplied interface certificate unchanged."""
    supplied = getattr(imported, "source_" + name, None)
    if supplied is not None:
        return supplied
    return _qualified(imported.namespace + ".Algo2LeanGenerated") + "." + name


def _dependency_facts(compiled):
    """Require determinism certificates for executable dependencies, not behavioral laws."""
    slots = getattr(compiled, "dependencies", {})
    bindings = getattr(compiled, "bindings", {})
    environments = getattr(compiled, "environments", {})
    lines = []
    if slots:
        lines.extend([
            "/-- Optional determinism evidence for the separately supplied interface code. -/",
            "structure DependencyFacts (dependencies : Dependencies) where",
        ])
        for slot in slots.values():
            lines.append("  «%s» : InterfaceFacts dependencies.«%s».toInterfaceCode" % (slot.field, slot.field))
        lines.append("")
    if bindings:
        from .interfaces import emit_binding_facts
        for name, binding in bindings.items():
            lines.extend([emit_binding_facts(binding, name=name), ""])
    for name, environment in environments.items():
        arguments = " (dependencies : Dependencies) (facts : DependencyFacts dependencies)" if slots else ""
        code = "(%s dependencies)" % name if slots else name
        lines.append("def %s_facts%s : %s.DependencyFacts %s where" %
                     (name, arguments, environment.target.namespace, code))
        for field, evidence in environment.facts.items():
            lines.append("  «%s» := %s" % (field, evidence))
        lines.append("")
    return lines


def emit_facts(compiled):
    """Emit optional Facts for a CompiledModule without changing its definitions.

    ``compiled`` supplies ``namespace``, ``lean_module``, ``lowered`` and
    ``imports``. The imports mapping contains each imported call's ``namespace``
    and unique caller ``frame`` constructor. Dependencies are deduplicated by
    that constructor, so aliases and repeated calls share one certificate.
    """
    lowered, imports = compiled.lowered, compiled.imports
    slots = getattr(compiled, "dependencies", {})
    bindings = getattr(compiled, "bindings", {})
    environments = getattr(compiled, "environments", {})
    dependencies = {}
    for imported in imports.values():
        previous = dependencies.setdefault(imported.frame, imported)
        if previous.namespace != imported.namespace:
            raise AssertionError("Imported frame constructor has conflicting modules")

    outer_namespace = _qualified(compiled.namespace)
    lines = ["import " + _qualified(compiled.lean_module)]
    fact_imports = []
    for imported in dependencies.values():
        if not getattr(imported, "interface_code", ""):
            fact_imports.append("Algo." + imported.module + ".Facts")
    fact_imports.extend(binding.backend.namespace + ".Facts" for binding in bindings.values())
    fact_imports.extend(environment.target.namespace + ".Facts" for environment in environments.values())
    lines.extend("import " + name for name in dict.fromkeys(_qualified(name) for name in fact_imports))
    lines.extend([
        "", "-- Optional proof certificate; execution remains the generated Step relation.",
        "namespace " + outer_namespace, "", "open Algo2LeanCore _root_.Algo2LeanGenerated", "",
    ])
    lines.extend(_dependency_facts(compiled))
    lines.extend(["namespace Algo2LeanGenerated", ""])
    if slots:
        from .module_parameters import emit_dependency_context
        lines.extend(emit_dependency_context(compiled))
    facts_argument = " (facts : DependencyFacts dependencies)" if slots else ""
    next_reference = "next dependencies facts" if slots else "next"
    step_next_reference = "step_next dependencies facts" if slots else "step_next"

    rules_by_function = {}
    for name, lowerer in lowered.items():
        rules = _source_rules(lowerer, lowered, imports)
        rules_by_function[name] = rules
        lines.append("private def next_%s (h : Heap) (s : State_%s) (stack : Stack) : Nat → Configuration" %
                     (name, name))
        for pc, node in enumerate(lowerer.nodes):
            if node.kind == "stuck":
                continue
            tag = "%s_pc%d" % (name, pc)
            if node.kind == "branch":
                condition = node.data[0]
                yes, no = rules[tag + "_true"][1], rules[tag + "_false"][1]
                successor = "if %s then %s else %s" % (condition, yes, no)
            else:
                successor = rules[tag][1]
            lines.append("  | %d => %s" % (pc, successor))
        lines.extend(["  | pc => .active h (.%s pc s) stack" % constructor(name), ""])

    lines.extend([
        "/-- A total projection used only to certify uniqueness of actual transitions. -/",
        "def next%s : Configuration → Configuration" % facts_argument,
        "  | .done h result => .done h result",
        "  | .active h frame stack => match frame with",
        "    | .invalid => .active h .invalid stack",
    ])
    for name in lowered:
        lines.append("    | .%s pc s => next_%s%s h s stack pc" %
                     (constructor(name), name, " dependencies" if slots else ""))
    for imported in dependencies.values():
        lines.extend([
            "    | .%s frame inner resume =>" % imported.frame,
            "      ModuleCall.config Frame.%s resume stack (%s (.active h frame inner))" %
            (imported.frame, _source_fact(imported, "next")),
        ])
    lines.extend([
        "", "/-- Each generated rule agrees with the projection; guards remain in Step. -/",
        "theorem step_next%s {before after : Configuration} (transition : Step before after) :" % facts_argument,
        "    %s before = after := by" % next_reference,
        "  cases transition" + (" with" if lowered or dependencies else ""),
    ])
    for name, rules in rules_by_function.items():
        for tag, (_, _, guarded) in rules.items():
            branch = tag.endswith("_true") or tag.endswith("_false")
            binders = "h s stack" + (" condition" if branch else " defined" if guarded else "")
            proof = "simp [next, next_%s, condition]" % name if branch else "rfl"
            lines.append("  | %s %s => %s" % (tag, binders, proof))
    for imported in dependencies.values():
        lines.extend([
            "  | %s h frame inner resume caller after transition =>" % imported.frame,
            "    exact congrArg (ModuleCall.config Frame.%s resume caller) (%s transition)" %
            (imported.frame, _source_fact(imported, "step_next")),
        ])
    lines.extend([
        "", "/-- Imported determinism composes without reopening imported transition rules. -/",
        "theorem deterministic%s : Deterministic Step := by" % facts_argument,
        "  intro before left right first second",
        "  exact (%s first).symm.trans (%s second)" % (step_next_reference, step_next_reference),
        "", "end Algo2LeanGenerated", "", "end " + outer_namespace, "",
    ])
    return "\n".join(lines)
