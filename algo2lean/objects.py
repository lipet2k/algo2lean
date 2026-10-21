"""Emit typed Lean views of mutable class objects.

The shared heap stores an open collection of tagged objects. Generated views
give each declared field its source type without imposing recursive validity on
an object graph: cycles and shared references are ordinary heap values.
"""

from .source_types import (is_collection, is_finite_collection, parse_type,
                           sequence_element, type_children, tuple_elements)


def tuple_value(values):
    """Construct a source tuple, preserving empty and singleton arities."""
    if not values:
        return "()"
    if len(values) == 1:
        return "(Tuple1.mk %s)" % values[0]
    return "(%s)" % ", ".join(values)


def tuple_projection(value, index, arity):
    """Project one source component without flattening nested tuple values."""
    assert 0 <= index < arity
    if arity == 1:
        return "(%s).value" % value
    return "(%s)" % value + ".2" * index + (".1" if index < arity - 1 else "")


def contains_tuple(typ):
    return tuple_elements(typ) is not None or any(contains_tuple(child) for child in type_children(typ))


def contains_real(typ):
    return typ == "Real" or any(contains_real(child) for child in type_children(typ))


def uses_reals(functions, classes=None):
    """Detect optional real semantics, including private locals and class fields."""
    for function in functions:
        if any(contains_real(typ) for typ in [function.return_type, *function.variables.values(),
                                             *function.expression_types.values()]):
            return True
        if any(contains_real(typ) for cls in function.classes.values() for typ in cls.fields.values()):
            return True
    return any(contains_real(typ) for cls in (classes or {}).values() for typ in cls.fields.values())


def uses_tuples(functions):
    for function in functions:
        if any(contains_tuple(typ) for typ in [function.return_type, *function.variables.values(),
                                              *function.expression_types.values()]):
            return True
        if any(contains_tuple(typ) for cls in function.classes.values() for typ in cls.fields.values()):
            return True
    return False


def uses_finite_collections(functions):
    return any(is_finite_collection(typ) for typ in collection_types(functions))


def collection_descriptor(typ):
    if is_finite_collection(typ):
        return "«" + parse_type(typ).name.lower() + "[" + ", ".join(type_children(typ)) + "]»"
    return sequence_descriptor(typ)


def value_codec(typ):
    """Use shared codecs; products retain their source arity in stored values."""
    elements = tuple_elements(typ)
    if elements is not None:
        if not elements:
            fields = "TupleFields.empty"
        elif len(elements) == 1:
            fields = "(TupleFields.singleton %s)" % value_codec(elements[0])
        else:
            fields = "(TupleFields.last %s)" % value_codec(elements[-1])
            for element in reversed(elements[:-1]):
                fields = "(TupleFields.cons %s %s)" % (value_codec(element), fields)
        return "(ValueCodec.tuple %s)" % fields
    name = ("collection" if is_collection(typ) else
            {"Int": "int", "Bool": "bool", "Real": "real", "Seq": "seq", "None": "unit"}.get(typ))
    if name is None:
        name = "nullableObject" if typ.endswith("?") else "object"
    return "ValueCodec." + name


def sequence_descriptor(typ):
    """Readable names for instantiated collection views, independent of labels."""
    element = sequence_element(typ)
    assert element is not None and typ != "Seq"
    if any(symbol in element for symbol in ("Tuple[", "Set[", "Dict[")):
        # Brackets cannot occur in source class names, so these structural names
        # cannot collide with the legacy underscore-based class descriptors.
        return "«seq[" + element + "]»"
    def stem(value):
        nested = sequence_element(value)
        if nested is not None:
            return "Seq_" + stem(nested)
        return value.replace("?", "_optional")
    return "seq_" + stem(element)


def collection_types(functions):
    """Collect only used specializations, including field and nested types."""
    found = set()
    def visit(typ):
        if is_collection(typ):
            found.add(typ)
        for child in type_children(typ):
            visit(child)
    for function in functions:
        for typ in [function.return_type, *function.variables.values(),
                    *function.expression_types.values()]:
            visit(typ)
        for definition in function.classes.values():
            for typ in definition.fields.values():
                visit(typ)
    return sorted(found)


def type_tag(typ, classes):
    """Canonical runtime type tag, independent of the caller's import spelling."""
    def tag(node):
        if node.arguments or node.name == "Tuple":
            return node.name + "[" + ", ".join(tag(child) for child in node.arguments) + "]"
        name = ((classes[node.name].runtime_tag or node.name)
                if node.name in classes else node.name)
        return name + ("?" if node.nullable else "")
    return tag(parse_type(typ))


def emit_collections(lines, types, classes=None):
    """One codec descriptor per used type; all operations live in the library."""
    classes = {} if classes is None else classes
    for typ in types:
        if is_finite_collection(typ):
            parts = type_children(typ)
            tag = lambda value: type_tag(value, classes or {})
            if len(parts) == 1:
                element = parts[0]
                lines.extend([
                    "def %s : SetType %s where" % (collection_descriptor(typ), raw_type(element)),
                    '  name := "%s"' % tag(element),
                    "  toValueCodec := %s" % value_codec(element),
                    "  keyEq := inferInstance", "",
                ])
            else:
                key, value = parts
                lines.extend([
                    "def %s : DictType %s %s where" % (collection_descriptor(typ), raw_type(key), raw_type(value)),
                    '  keyName := "%s"' % tag(key),
                    '  valueName := "%s"' % tag(value),
                    "  key := %s" % value_codec(key),
                    "  value := %s" % value_codec(value),
                    "  keyEq := inferInstance", "",
                ])
            continue
        element = sequence_element(typ)
        lines.extend([
            "def %s : SequenceType %s where" % (sequence_descriptor(typ), raw_type(element)),
            '  name := "%s"' % type_tag(element, classes),
            "  encode := fun value => %s" % encode(element, "value"),
            "  decode := %s" % decoder(element),
            "  decode_encode := %s.decode_encode" % value_codec(element)
            if tuple_elements(element) is not None or element == "Real" else
            "  decode_encode := by intro value; cases value <;> rfl" if element.endswith("?") or element == "None"
            else "  decode_encode := by intro value; rfl",
            "",
        ])


def raw_type(typ):
    """The Lean representation of a statically checked source type."""
    elements = tuple_elements(typ)
    if elements is not None:
        if not elements:
            return "Unit"
        if len(elements) == 1:
            return "(Tuple1 %s)" % raw_type(elements[0])
        return "(%s)" % " × ".join(raw_type(element) for element in elements)
    if typ == "Seq":
        return "SeqRef"
    if is_collection(typ):
        return "CollectionRef"
    if typ == "None":
        return "Unit"
    if typ in {"Int", "Bool", "Real"}:
        return typ
    if typ.endswith("?"):
        return "(Option Ref_%s)" % typ[:-1]
    return "Ref_%s" % typ


def default_value(typ):
    """Return a frame or decoder fallback value without marking a source field initialized."""
    elements = tuple_elements(typ)
    if elements is not None:
        return tuple_value([default_value(element) for element in elements])
    if typ == "Bool":
        return "false"
    if typ == "None":
        return "()"
    if typ.endswith("?"):
        return "none"
    return "0"


def encode(typ, value):
    """Store a value in the heterogeneous field arena."""
    if tuple_elements(typ) is not None or typ == "Real":
        return "(%s.encode %s)" % (value_codec(typ), value)
    constructor = "collectionValue" if is_collection(typ) else {"Int": "intValue", "Bool": "boolValue", "Seq": "seqValue"}.get(typ)
    if constructor:
        return "(ObjectValue.%s %s)" % (constructor, value)
    if typ == "None":
        return "ObjectValue.noneValue"
    if typ.endswith("?"):
        return ("(match %s with | some ref => ObjectValue.objectValue ref "
                "| none => ObjectValue.noneValue)") % value
    return "(ObjectValue.objectValue %s)" % value


def decoder(typ):
    """The partial decoder; missing/uninitialized remains distinct from null."""
    if tuple_elements(typ) is not None or typ == "Real":
        return "%s.decode" % value_codec(typ)
    name = "asCollection" if is_collection(typ) else {"Int": "asInt", "Bool": "asBool", "Seq": "asSeq", "None": "asNone"}.get(typ)
    if name is None:
        name = "asNullableObject" if typ.endswith("?") else "asObject"
    return "ObjectValue.%s" % name


def emit_classes(lines, classes):
    """Emit stable class declarations before function state structures."""
    # Declare all references first so fields can refer forward or recursively.
    for name in classes:
        definition = classes[name]
        reference = (definition.imported_from + ".Algo2LeanGenerated.Ref_" + definition.imported_name
                     if definition.imported_from and not definition.is_interface else "ObjectRef")
        lines.append("abbrev Ref_%s := %s" % (name, reference))
    if classes:
        lines.append("")
    for name, definition in classes.items():
        if definition.is_interface:
            continue  # Membership depends on the selected executable interface.
        if definition.imported_from:
            prefix = definition.imported_from + ".Algo2LeanGenerated."
            original = definition.imported_name
            lines.append("abbrev is_%s := %sis_%s" % (name, prefix, original))
            lines.append("abbrev create_%s := %screate_%s" % (name, prefix, original))
            for field in definition.fields:
                for stem in ("field", "set"):
                    lines.append("abbrev %s_%s_%s := %s%s_%s_%s" % (stem, name, field, prefix, stem, original, field))
            lines.append("")
            continue
        tag = definition.runtime_tag or name
        lines.extend([
            "-- Shallow class membership; fields and referenced objects are observed separately.",
            'def is_%s (h : Heap) (ref : Ref_%s) : Prop :=' % (name, name),
            '  ref < h.nextObject ∧ h.objectClass ref = some "%s"' % tag,
            "instance (h : Heap) (ref : Ref_%s) : Decidable (is_%s h ref) :=" % (name, name),
            '  inferInstanceAs (Decidable (ref < h.nextObject ∧ h.objectClass ref = some "%s"))' % tag,
            "",
        ])
        for field, typ in definition.fields.items():
            getter, setter = "field_%s_%s" % (name, field), "set_%s_%s" % (name, field)
            lines.extend([
                "def %s (h : Heap) (ref : Ref_%s) : Option %s :=" % (getter, name, raw_type(typ)),
                '  if is_%s h ref then (h.readField ref "%s").bind %s else none' % (name, field, decoder(typ)),
                "def %s (h : Heap) (ref : Ref_%s) (%s : %s) : Heap :=" % (setter, name, "_value" if typ == "None" else "value", raw_type(typ)),
                '  h.writeField ref "%s" %s' % (field, encode(typ, "value")),
                "@[simp] theorem %s_set (h : Heap) (ref : Ref_%s) (value : %s)" % (getter, name, raw_type(typ)),
                "    (valid : is_%s h ref) :" % name,
                "    %s (%s h ref value) ref = some value := by" % (getter, setter),
                "  have valid' : is_%s (%s h ref value) ref := by" % (name, setter),
                "    simpa [%s, is_%s] using valid" % (setter, name),
                "  rw [%s, if_pos valid']" % getter,
                "  unfold %s" % setter,
                '  rw [Heap.readField_writeField_same h ref "%s" _ "%s" valid.2]' % (field, tag),
            ])
            if tuple_elements(typ) is not None or typ == "Real":
                lines.append("  exact %s.decode_encode value" % value_codec(typ))
            elif typ.endswith("?") or typ == "None":
                lines.append("  cases value <;> rfl")
            else:
                lines.append("  rfl")
            lines.append("")
        parameters = " ".join("(value_%s : %s)" % (field, raw_type(typ))
                              for field, typ in definition.fields.items())
        lines.extend([
            "/-- Build input data directly; this helper does not execute `__init__`. -/",
            "def create_%s (h : Heap)%s : Heap × Ref_%s :=" % (name, " " + parameters if parameters else "", name),
            "  let ref := h.nextObject",
            '  let h := h.allocateObject "%s"' % tag,
        ])
        for field in definition.fields:
            lines.append("  let h := set_%s_%s h ref value_%s" % (name, field, field))
        lines.extend(["  (h, ref)", ""])
