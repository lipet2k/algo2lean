"""Source-facing names and metadata for the Lean proof interface.

Generated declarations use these scoped names directly. Historical spellings
remain in migration mappings only; they are not emitted into Lean modules.
"""

# Source identifiers are ASCII, but some are keywords in Lean rather than
# Python. Quote reserved components and leave other identifiers unchanged.
_LEAN_KEYWORDS = set("""_ _root_ abbrev alias assert assume at attribute axiom axioms by case cases
class coinductive constant constants constructor def deriving do else end example
exists export extends forall from fun have if import in include inductive
infix infixl infixr init instance let macro macro_rules match mutual namespace
noncomputable notation opaque open partial prelude private protected quotient
return scoped section set_option show structure syntax then theorem universe
universes unsafe using variable variables where with elab elab_rules lemma
termination_by decreasing_by try catch finally for while unless calc suffices Prop Type Sort
""".split())

PROBABILITY_MEMBERS = ("outcome", "law", "returnProbability", "outputProbability",
                       "terminationProbability", "cost", "expectedCost", "costProbability",
                       "expectedReturn", "expectedFrom", "HasLaw", "returnProbability_eq_expectedReturn")


def identifier(name):
    # Lean interprets _root_ specially even inside guillemets. The extra dot
    # cannot collide with an ASCII source identifier, so the name remains distinct.
    if name == "_root_":
        return "«_root_·»"
    return "«%s»" % name if name in _LEAN_KEYWORDS else name


def function_namespace(function):
    parts = (function.class_name, function.method_name) if function.class_name else (function.name,)
    return ".".join(identifier(part) for part in parts)


def function_reference(function, member, namespace="", dependencies=False):
    """Qualify references independently of source names and proof binders."""
    prefix = "_root_." + (namespace + "." if namespace else "")
    name = prefix + function_namespace(function) + "." + member
    if member == "load":
        return name
    if member == "ValidInput":
        dependencies = dependencies and any(
            function.classes.get(typ.rstrip("?")) is not None and
            function.classes[typ.rstrip("?")].is_interface
            for _, typ in function.parameters)
    return name + (" dependencies" if dependencies else "")


def public_aliases(function, has_clocks=False):
    name = function.name
    aliases = [("ValidInput", "validInputs_" + name), ("initial", "initial_" + name),
               ("Run", "is_Execution_" + name), ("Call", "is_Summary_" + name),
               ("CallFrom", "is_SummaryFrom_" + name), ("load", "load_" + name),
               ("ValidHeapTranscript", "is_HeapTranscript_" + name),
               ("ValidTranscript", "is_Transcript_" + name), ("Returns", "is_Output_" + name)]
    if has_clocks:
        aliases += [("ReturnsWithCost", "is_OutputWithCost_" + name)]
    return [(function_namespace(function) + "." + public, legacy) for public, legacy in aliases]


def point_aliases(function):
    from .source_types import is_sequence
    prefix = function_namespace(function)
    aliases, variables = [], {}
    for point in function.points.values():
        aliases.append((prefix + ".At." + identifier(point["name"]),
                        "At_%s_%s" % (function.name, point["name"])))
        variables.update((variable["name"], variable["type"]) for variable in point["variables"])
    for name, typ in variables.items():
        aliases.append((prefix + ".Local." + identifier(name), "local_%s_%s" % (function.name, name)))
        if is_sequence(typ):
            aliases.append((prefix + ".Element." + identifier(name), "element_%s_%s" % (function.name, name)))
    return aliases


def interface_entries(function, has_clocks, *, dependencies=False, facts=False,
                      randomized=False, probability=False, parallel=False):
    """Describe emitted declarations using the emitter's actual Lean types.

    Names are relative to the generated module namespace. Facts are optional
    project declarations; probability declarations require their optional
    companion. Neither option changes the algorithm definitions.
    """
    from .emitter import input_needs_heap, lean_type, object_type, public_types, tuple_type, valid_value
    from .source_types import is_sequence, sequence_element

    name = function_namespace(function)
    value_input, value_output = public_types(function)
    raw_input, raw_output = tuple_type(function.parameters), lean_type(function.return_type)
    configuration = "Configuration dependencies" if dependencies else "Configuration"
    transcript = "Transcript dependencies" if dependencies else "Transcript"
    entries = []

    def argument(name, typ, meaning, implicit=False, anonymous=False):
        return {"name": name, "type": typ, "meaning": meaning, "implicit": implicit, "anonymous": anonymous}

    def dependency(implicit=False):
        return [argument("dependencies", "Dependencies", "Executable implementations of the module's interfaces.", implicit)] if dependencies else []

    def add(member, category, arguments, result, meaning, file_kind="core", **location):
        preferred = name + "." + member
        binders = []
        for item in arguments:
            if item["anonymous"]:
                continue
            left, right = ("{", "}") if item["implicit"] else ("(", ")")
            binders.append(left + item["name"] + " : " + item["type"] + right)
        result = " → ".join([item["type"] for item in arguments if item["anonymous"]] + [result])
        entries.append({"name": preferred, "category": category,
            "signature": preferred + (" " + " ".join(binders) if binders else "") + " : " + result,
            "meaning": meaning, "arguments": arguments, "file_kind": file_kind, **location})

    source_arguments = ", ".join(parameter for parameter, _ in function.parameters) or "no source arguments"
    ordinary_input = "Input heap and arguments (%s), preserving shared references." % source_arguments if input_needs_heap(function) else "Mathematical input values (%s)." % source_arguments
    if not input_needs_heap(function) and any(typ == "Seq" for _, typ in function.parameters):
        ordinary_input += " Each integer sequence input is loaded separately."
    raw_input_meaning = "Reference-level arguments (%s), preserving shared references." % source_arguments
    output_meaning = "Returned mathematical value."
    if function.return_type == "Seq":
        output_meaning = "Returned sequence contents, represented as an Int → Int function."
    elif object_type(function.return_type):
        output_meaning = "Pair of the final heap and the returned object or typed-sequence reference."
    raw_output_meaning = "Returned value; mutable sequences and objects are represented by references."
    before = argument("before", "Heap", "Heap before execution, including existing references and counters.")
    after = argument("after", "Heap", "Heap after the completed execution.")
    raw_args = [before, argument("input", raw_input, raw_input_meaning), after,
                argument("output", raw_output, raw_output_meaning)]
    values = [argument("input", value_input, ordinary_input), argument("output", value_output, output_meaning)]
    costs = argument("costs", "Clocks", "Increments of named tick counters during this same execution.")
    value_parameters = [dict(item, name="my_" + item["name"]) for item in values]
    heap_parameters = [dict(item, name={"before": "h", "after": "h'"}.get(item["name"], item["name"])) for item in raw_args]
    add("Returns", "output", dependency() + value_parameters, "Prop",
        "A possible completed execution returns this value; this does not assign a probability." if randomized else
        "The function completes with this returned value.")
    if has_clocks:
        add("ReturnsWithCost", "output", dependency() + value_parameters + [costs], "Prop",
            "One possible completed execution produces both this value and these tick-counter increments; this does not assign a probability." if randomized else
            "One completed execution produces both the returned value and these tick-counter increments.")
    add("Call", "execution", dependency() + heap_parameters, "Prop",
        "Valid inputs and a possible completed call with these heap effects, reusable under any caller stack; this does not assert a probability or almost-sure termination." if randomized else
        "Valid inputs and a completed call with these heap effects, reusable under any caller stack.")
    add("Run", "execution", dependency() + heap_parameters, "Prop",
        "Valid inputs and a possible completed execution with this final heap and returned value; this does not assign a probability." if randomized else
        "Valid inputs and a completed execution with this final heap and returned value.")
    add("CallFrom", "execution", dependency() + [argument("state", configuration, "Current local configuration of this function."),
        dict(after, name="finalHeap"), argument("output", raw_output, raw_output_meaning)], "Prop",
        "A possible completion of this function from the supplied local state under any caller stack; this does not assign a probability." if randomized else
        "Complete this function from the supplied local state under any caller stack.")
    trace = argument("trace", transcript, "Finite list containing the initial configuration and every subsequent configuration.")
    add("ValidTranscript", "transcript", dependency() + [value_parameters[0], trace],
        "Prop", "A valid finite execution prefix from the loaded input; it need not have returned.")
    add("ValidHeapTranscript", "transcript", dependency() + heap_parameters[:2] + [trace], "Prop",
        "Valid reference inputs and a finite execution prefix from the supplied heap.")
    validity_depends = dependencies and any(
        function.classes.get(typ.rstrip("?")) is not None and function.classes[typ.rstrip("?")].is_interface
        for _, typ in function.parameters)
    validity_checks = any(valid_value(typ, "input") is not None for _, typ in function.parameters)
    validity_parameters = heap_parameters[:2] if validity_checks else [dict(before, name="_h"), dict(raw_args[1], name="_input")]
    add("ValidInput", "input", (dependency() if validity_depends else []) + validity_parameters, "Prop",
        "The input validity conditions required by execution, including applicable reference checks.")
    add("initial", "input", dependency() + [heap_parameters[0], dict(raw_args[1], name="input" if function.parameters else "_input")], configuration,
        "Build the root entry configuration; this does not establish input validity.")
    add("load", "input", [dict(values[0], name="input" if function.parameters else "_input")], "Heap × (%s)" % raw_input,
        "Convert the ordinary input view to a heap and reference-level arguments.")

    if parallel:
        add("ParallelCall", "execution", dependency() + [dict(item, name="finalHeap") if item["name"] == "h'" else item for item in heap_parameters] + [
            argument("cost", "Algo2LeanParallel.Cost", "Work and span of this same structured fork-join execution, including primitive, call, and synchronization costs."),
            argument("access", "Algo2LeanParallel.Access", "Memory accesses of this execution; every fork must establish that its children do not interfere.")], "Prop",
            "A completed structured fork-join call with its final heap, returned value, work, span, and memory accesses. Forked children must satisfy the parallel safety conditions.")

    if probability:
        law_arguments = [dict(before, name="heap"), argument("input", raw_input, raw_input_meaning)]
        add("HasLaw", "probability", law_arguments + [argument("distribution", "PMF (Heap × (%s))" % raw_output,
            "Joint probability mass function of the final heap and returned value, retaining counters and shared references.")], "Prop",
            "Reusable joint return law: every nonnegative heap/output reward has the expectation specified by this distribution. This includes almost-sure successful termination.", "probability")
        add("expectedReturn", "probability", law_arguments + [argument("reward", "Heap → %s → ENNReal" % raw_output,
            "Nonnegative reward of the joint final heap and returned value, for example a function of output and clock increments.")], "ENNReal",
            "Unconditional expected reward on successful return. Failed or diverging calls contribute zero; use cost observations to include their work.", "probability")
        add("expectedFrom", "probability", [argument("state", configuration,
            "Local configuration of this function; its suspended caller stack is ignored."),
            argument("reward", "Heap → %s → ENNReal" % raw_output, "Reward of the final heap and returned value.")], "ENNReal",
            "Expected return reward from this function's current local state, independent of any caller. No reachability or input-validity premise is built in. Other functions and completed states give zero.", "probability")
        add("outputProbability", "probability", values, "ENNReal",
            "Unconditional probability of returning this mathematical output. Failure and divergence are not conditioned away.", "probability")
        add("terminationProbability", "probability", law_arguments, "ENNReal",
            "Probability of returning successfully, with no bound on duration. Failed and diverging executions do not count as successful termination.", "probability")
        add("expectedCost", "probability", law_arguments + [argument("clock", "String", "Name of the tick counter to measure.")], "ENNReal",
            "Expected increase of this tick counter over all finite prefixes, including failed or nonterminating executions; it may be infinite.", "probability")
        add("cost", "probability", [dict(before, name="heap"), argument("clock", "String", "Name of the tick counter to measure.")],
            "Algo2LeanProbability.Observable Configuration",
            "Total clock increase on each execution, including failure and divergence. Combine this observation with other costs or apply a measurable function to study moments and nonlinear rewards.", "probability")
        add("costProbability", "probability", law_arguments + [argument("clock", "String", "Name of the tick counter to measure."),
            argument("threshold", "ENNReal", "Strict lower threshold for the total clock increase.")], "ENNReal",
            "Probability that this clock's total increase exceeds the threshold, including costs on executions that fail or never return.", "probability")
        add("returnProbability", "probability", law_arguments + [argument("post", "Heap → %s → Prop" % raw_output,
            "Joint condition on the final heap and returned reference-level value.")], "ENNReal",
            "Unconditional probability of returning successfully with this heap/output postcondition. Failure and divergence are not conditioned away.", "probability")
        add("returnProbability_eq_expectedReturn", "probability", law_arguments + [
            argument("valid", name + ".ValidInput heap input", "The source arguments satisfy this function's input conditions."),
            argument("post", "Heap → %s → Prop" % raw_output, "Property of the successful final heap and returned value.")],
            name + ".returnProbability heap input post = " + name +
            ".expectedReturn heap input (fun final value => if post final value then 1 else 0)",
            "Rewrite a return probability as the expected zero-or-one reward, allowing reuse of the same completed-call contract.", "probability")
        add("law", "probability", law_arguments, "MeasureTheory.Measure (Algo2LeanProbability.Run Configuration)",
            "Probability measure on the whole execution, including successful returns, errors, and divergence. Each reached draw is fresh and uniform on its current interval.", "probability")
        add("outcome", "probability", [argument("state", configuration,
            "Configuration to inspect for a successful return of this function.", anonymous=True)], "Option (Heap × (%s))" % raw_output,
            "Read a successful return of this function as its final heap and reference-level value; otherwise none.", "probability")

    applied = " dependencies" if dependencies else ""
    call_type = name + ".Call" + applied + " before input after output"
    run_type = name + ".Run" + applied + " before input after output"
    call_context = [dict(item, implicit=True) for item in raw_args]
    add("Call.run", "helper", dependency(True) + call_context + [argument("call", call_type, "Reusable completed-call proof.")], run_type,
        "Use a reusable call proof as a completed root execution.")
    if probability and not randomized and not dependencies:
        add("Call.hasLaw", "probability", call_context + [
            argument("call", call_type, "An existing terminating deterministic call proof.")],
            name + ".HasLaw before input (PMF.pure (after, output))",
            "Reuse a deterministic proof as the joint final-heap/output law, retaining mutation and counters.", "probability")
        add("Call.expectedReturn", "probability", call_context + [
            argument("call", call_type, "An existing terminating deterministic call proof."),
            argument("reward", "Heap → %s → ENNReal" % raw_output, "Joint reward of the final heap and returned value.")],
            name + ".expectedReturn before input reward = reward after output",
            "Evaluate a probabilistic caller's continuation using the existing deterministic analysis.", "probability")
    if parallel:
        parallel_context = call_context + [
            argument("cost", "Algo2LeanParallel.Cost", "Work and span of the completed parallel execution.", True),
            argument("access", "Algo2LeanParallel.Access", "Access record of the same execution.", True)]
        add("ParallelCall.call", "helper", dependency(True) + parallel_context + [
            argument("run", name + ".ParallelCall" + applied + " before input after output cost access",
                     "Completed parallel-call proof, including its safety obligations.")], call_type,
            "Obtain the ordinary call for the same final heap and result by serializing the structured parallel execution.")
    if has_clocks:
        returns = name + ".Returns" + applied + " input output"
        with_cost = name + ".ReturnsWithCost" + applied + " input output costs"
        value_context = [dict(item, implicit=True) for item in values]
        add("ReturnsWithCost.returns", "output", dependency(True) + value_context + [dict(costs, implicit=True),
            argument("run", with_cost, "Proof of the returned value and its costs on one execution.")], returns,
            "Forget the cost observation while retaining the same returned value.")
        add("Returns.withCost", "output", dependency(True) + value_context + [argument("run", returns, "Proof of a completed output.")],
            "∃ costs, " + with_cost, "Expose the counter increments of the same completed execution.")
    if facts:
        evidence = [argument("facts", "DependencyFacts dependencies", "Determinism evidence for the chosen interface implementations.")] if dependencies else []
        expected_heap = argument("expectedHeap", "Heap", "Final heap specified by the call proof.", True)
        expected = argument("expected", raw_output, "Returned value specified by the call proof.", True)
        context = [call_context[0], call_context[2], expected_heap, call_context[1], call_context[3], expected]
        add("Run.eq_of_call", "helper", dependency(True) + evidence + context + [argument("run", run_type, "Any completed execution on these inputs."),
            argument("call", name + ".Call" + applied + " before input expectedHeap expected", "Reusable specification for the same inputs.")],
            "after = expectedHeap ∧ output = expected", "Every completed execution agrees with the supplied call proof. Requires the optional Facts module.", "facts")

    variables = {}
    for point in function.points.values():
        add("At." + identifier(point["name"]), "location", dependency() + [argument("state", configuration, "The local configuration to inspect; no reachability assumption is needed.", anonymous=True)],
            "Prop", "The configuration is at # @%s, before its labeled statement; no reachability is assumed." % point["name"], "points",
            line=point["line"], column=point["column"])
        variables.update((variable["name"], variable["type"]) for variable in point["variables"])
    for variable, typ in variables.items():
        state = argument("state", configuration, "Local configuration containing the variable and its heap.")
        add("Local." + identifier(variable), "observation", dependency() + [dict(state, anonymous=True)], "Option " + lean_type(typ),
            "Observe source variable %s at named locations where it is available; otherwise none." % variable, "points")
        if is_sequence(typ):
            add("Element." + identifier(variable), "observation", dependency() + [state, argument("index", "Int", "Integer index to read from the observed sequence.")],
                "Option " + lean_type(sequence_element(typ)),
                "Read an element of %s in the current heap; none when the observation or typed element is unavailable." % variable, "points")
    return entries


def interface_metadata(function, has_clocks, *, dependencies=False, facts=False,
                       randomized=False, probability=False, parallel=False):
    name = function_namespace(function)
    return {"lean_name": name, "output_relation": name + ".Returns",
            "transcript_relation": name + ".ValidTranscript",
            "cost_relation": name + ".ReturnsWithCost" if has_clocks else None,
            "interface_entries": interface_entries(function, has_clocks, dependencies=dependencies, facts=facts,
                                                   randomized=randomized, probability=probability, parallel=parallel)}
