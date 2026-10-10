"""Emit checked summary transfers for an unchanged component in a larger program.

The certificate translates control state and proves every component transition
against the target compiler output. It imports previously checked modules; it
never copies or concatenates an analysis proof.
"""

import ast
import re

from .compiler import Lowerer, compile_source
from .emitter import constructor, emit_step, lean_type, tuple_type
from .frontend import CompileError, parse_program
from .modules import validate_module_name
from .public_names import function_namespace


def _module_name(name):
    if not isinstance(name, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", name):
        raise CompileError("Embedding imports must be safe Lean module names.")
    return ".".join("«%s»" % part for part in name.split("."))


def _namespace_name(name):
    if name is None:
        return ""
    try:
        validate_module_name(name)
    except ValueError as error:
        raise CompileError(str(error)) from None
    return "«%s»." % name


def _lower(source):
    # Keep diagnostics, resource limits, types, and reserved names identical to
    # ordinary compilation before constructing the checked correspondence.
    compile_source(source)
    functions, classes = parse_program(ast.parse(source, mode="exec", type_comments=True))
    return {name: Lowerer(function) for name, function in functions.items()}, classes


def _fingerprint(lowerer):
    function = lowerer.function
    return (function.parameters, function.return_type, list(function.variables.items()),
            list(lowerer.field_types.items()), lowerer.entry,
            [(node.kind, node.data) for node in lowerer.nodes])


def emit_embedding(source_source, target_source, *, source_module="LibraryGenerated",
                   target_module="ApplicationGenerated", source_namespace="Library",
                   target_namespace=None, namespace="LibraryEmbedding"):
    """Build a Lean-checked embedding of an unchanged source component.

    The source must be compiled with ``source_namespace`` and the target with
    ``target_namespace``. Module names can be safely qualified for cached proof
    libraries. The comparison ignores source positions and labels, but rejects
    changed declarations, data layouts, and lowered instructions.
    """
    source_import, target_import = _module_name(source_module), _module_name(target_module)
    source_prefix, target_prefix = _namespace_name(source_namespace), _namespace_name(target_namespace)
    if namespace is None:
        raise CompileError("The embedding needs its own namespace.")
    embedding_namespace = _namespace_name(namespace)[:-1]
    if source_prefix == target_prefix:
        raise CompileError("Component and application must use distinct generated namespaces.")
    source, source_classes = _lower(source_source)
    target, target_classes = _lower(target_source)
    for name, definition in source_classes.items():
        other = target_classes.get(name)
        if other is None or definition.fields != other.fields or definition.methods != other.methods:
            raise CompileError("Component class '%s' is missing or changed in the application." % name)
    for name, lowerer in source.items():
        if name not in target:
            raise CompileError("Component function '%s' is missing from the application." % name)
        if _fingerprint(lowerer) != _fingerprint(target[name]):
            raise CompileError("Component function '%s' has changed in the application." % name)

    sf, tf = source_prefix + "Algo2LeanGenerated", target_prefix + "Algo2LeanGenerated"
    lines = ["import " + source_import, "import " + target_import,
             "import Algo2LeanLib.Embedding", "",
             "set_option backward.isDefEq.respectTransparency false",
             "set_option backward.defeqAttrib.useBackward true", "",
             "namespace " + embedding_namespace, "",
             "open Algo2LeanCore _root_.Algo2LeanGenerated", "",
             "-- Translate only the component's control representation; the shared heap is unchanged."]
    for name, lowerer in source.items():
        fields = list(lowerer.field_types) or ["unused"]
        lines += ["def state_%s (s : %s.State_%s) : %s.State_%s :=" % (name, sf, name, tf, name),
                  "  { %s }" % ", ".join("%s := s.%s" % (field, field) for field in fields), ""]
    lines += ["def encodeFrame : %s.Frame → %s.Frame" % (sf, tf), "  | .invalid => .invalid"]
    for name in source:
        lines.append("  | .%s pc s => .%s pc (state_%s s)" % (constructor(name), constructor(name), name))
    lines += ["", "def encodeResult : %s.Result → %s.Result" % (sf, tf)]
    for name in source:
        lines.append("  | .%s value => .%s value" % (constructor(name), constructor(name)))
    lines += ["", "def decodeResult : %s.Result → Option %s.Result" % (tf, sf)]
    for name in target:
        lines.append("  | .%s %s => %s" % (constructor(name), "value" if name in source else "_",
            "some (.%s value)" % constructor(name) if name in source else "none"))
    lines += ["", "def embedding : CallEmbedding %s.Frame %s.Result %s.Frame %s.Result where" % (sf, sf, tf, tf),
              "  encodeFrame := encodeFrame", "  encodeResult := encodeResult", "  decodeResult := decodeResult",
              "  invalidFrame := .invalid", "  decode_encode := by intro result; cases result <;> rfl", ""]

    lines += ["-- Every source rule is checked against the actual corresponding application rule.",
              "theorem simulates : embedding.Simulates %s.Step %s.Step := by" % (sf, tf),
              "  intro caller before after transition", "  cases transition with"]
    for name, lowerer in source.items():
        emitted = []
        emit_step(emitted, lowerer, source)
        for line in emitted:
            match = re.match(r"  \| ([A-Za-z_0-9]+) \(h : Heap\)", line)
            if not match:
                continue
            tag = match.group(1)
            premise = " defined" if " (defined :" in line else " condition" if " (condition :" in line else ""
            pc = int(re.search(r"_pc(\d+)(?:_(?:true|false))?$", tag).group(1))
            node = lowerer.nodes[pc]
            target_step = "(%s.Step.%s h (state_%s s) (embedding.stack stack ++ caller)%s)" % (tf, tag, name, premise)
            lines.append("  | %s h s stack%s =>" % (tag, premise))
            if node.kind == "call":
                # Compiled match expressions in different modules need
                # extensional equality, even when their source branches agree.
                lines += ["    simp only [CallEmbedding.config_active, CallEmbedding.stack_cons, List.cons_append]",
                          "    apply Eq.mp ?_ " + target_step,
                          "    congr 4", "    all_goals (funext value; cases value <;> rfl)"]
            else:
                simp = ["CallEmbedding.config_active"]
                if node.kind == "return":
                    simp.append("CallEmbedding.resume")
                simp += ["embedding", "encodeFrame", "encodeResult", "state_" + name]
                lines += ["    simpa only [%s] using!" % ", ".join(simp), "      " + target_step]
    lines.append("")
    for name, lowerer in source.items():
        function = lowerer.function
        # Raw input/output representations agree definitionally; qualifying the
        # source views avoids accidental reliance on opened target names.
        raw_input = tuple_type(function.parameters)
        raw_output = lean_type(function.return_type)
        for cls in source_classes:
            raw_input = re.sub(r"\bRef_%s\b" % re.escape(cls), sf + ".Ref_" + cls, raw_input)
            raw_output = re.sub(r"\bRef_%s\b" % re.escape(cls), sf + ".Ref_" + cls, raw_output)
        lines += ["theorem summary_%s {before after : Heap} {input : %s} {output : %s}" % (name, raw_input, raw_output),
                  "    (contract : %s%s.Call before input after output) :" % (source_prefix, function_namespace(function)),
                  "    %s%s.Call before input after output := by" % (target_prefix, function_namespace(function)),
                  "  refine ⟨contract.1, ?_⟩",
                  "  simpa only [embedding, encodeFrame, encodeResult, state_%s] using!" % name,
                  "    embedding.summary simulates contract.2", ""]
    lines += ["end " + embedding_namespace, ""]
    return "\n".join(lines)
