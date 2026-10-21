"""Structural source types with stable canonical spellings.

Compiler stages exchange strings for compatibility. Parsing those strings into
one immutable tree keeps nested collection, tuple, and class transformations
consistent. This module describes types; the frontend decides which language
features and class declarations are available in a particular compilation.
"""

from dataclasses import dataclass
from functools import lru_cache
import re
from typing import Callable, Iterable, Optional, Tuple


_PRIMITIVES = frozenset({"Int", "Bool", "Real", "None"})
_CONSTRUCTORS = frozenset({"Seq", "Tuple", "Set", "Dict"})
_ARITIES = {"Seq": 1, "Set": 1, "Dict": 2}
_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z")


@dataclass(frozen=True)
class SourceType:
    """A scalar/class name or a constructor applied to structural arguments.

    Nullable class references retain the class name and set ``nullable``. ``Seq``
    always has an explicit element in the tree, even when rendered as bare ``Seq``.
    """

    name: str
    arguments: Tuple["SourceType", ...] = ()
    nullable: bool = False

    def __post_init__(self):
        if not isinstance(self.name, str) or not _NAME.fullmatch(self.name):
            raise ValueError("Invalid source type name: %r." % self.name)
        if not isinstance(self.arguments, tuple) or any(
                not isinstance(argument, SourceType) for argument in self.arguments):
            raise TypeError("Source type arguments must be a tuple of SourceType values.")
        if self.name in _ARITIES and len(self.arguments) != _ARITIES[self.name]:
            raise ValueError("%s expects %d type argument(s)." % (self.name, _ARITIES[self.name]))
        if self.name not in _CONSTRUCTORS and self.arguments:
            raise ValueError("%s does not accept type arguments." % self.name)
        if self.nullable and (self.name in _PRIMITIVES or self.name in _CONSTRUCTORS):
            raise ValueError("Only class references can be nullable.")


def _split_arguments(text: str) -> Tuple[str, ...]:
    """Split constructor arguments without splitting a nested constructor."""
    arguments, start, depth = [], 0, 0
    for index, character in enumerate(text):
        if character == "[":
            depth += 1
        elif character == "]":
            depth -= 1
            if depth < 0:
                raise ValueError("Unbalanced source type brackets.")
        elif character == "," and depth == 0:
            arguments.append(text[start:index].strip())
            start = index + 1
    if depth:
        raise ValueError("Unbalanced source type brackets.")
    arguments.append(text[start:].strip())
    # A trailing comma is the ordinary spelling for a singleton argument list.
    if len(arguments) > 1 and arguments[-1] == "":
        arguments.pop()
    if not arguments or any(not argument for argument in arguments):
        raise ValueError("A source type argument cannot be empty.")
    return tuple(arguments)


@lru_cache(maxsize=4096)
def parse_type(typ: str) -> SourceType:
    """Parse an internal source type, rejecting unknown constructors and arities.

    Class names may be qualified by their source module. Nullable references use
    the compiler's existing ``Class?`` spelling; source ``Class | None`` syntax
    remains the frontend's responsibility.
    """
    if not isinstance(typ, str):
        raise TypeError("A source type spelling must be a string.")
    spelling = typ.strip()
    nullable = spelling.endswith("?")
    if nullable:
        spelling = spelling[:-1].strip()
    if "[" not in spelling:
        if spelling == "Seq":
            return SourceType("Seq", (SourceType("Int"),), nullable)
        if spelling in {"Tuple", "Set", "Dict"}:
            raise ValueError("%s requires type arguments." % spelling)
        return SourceType(spelling, nullable=nullable)
    name, contents = spelling.split("[", 1)
    name = name.strip()
    if name not in _CONSTRUCTORS:
        raise ValueError("Unknown source type constructor: %s." % name)
    if not contents.endswith("]"):
        raise ValueError("Unbalanced source type brackets.")
    contents = contents[:-1].strip()
    if name == "Tuple" and contents == "()":
        arguments = ()
    else:
        arguments = tuple(parse_type(argument) for argument in _split_arguments(contents))
    return SourceType(name, arguments, nullable)


@lru_cache(maxsize=4096)
def render_type(typ: SourceType) -> str:
    """Render a canonical spelling; integer sequences retain the name ``Seq``."""
    if typ.name == "Seq" and typ.arguments == (SourceType("Int"),):
        return "Seq"
    if typ.name == "Tuple" and not typ.arguments:
        return "Tuple[()]"
    if typ.arguments:
        return "%s[%s]" % (typ.name, ", ".join(map(render_type, typ.arguments)))
    return typ.name + ("?" if typ.nullable else "")


def map_type(typ: str, rename_atom: Callable[[str], str]) -> str:
    """Rename scalar/class leaves, preserving constructors and nullable flags.

    The callback receives bare names, including primitive names, and returns a
    bare name. It can therefore resolve imported class aliases without knowing
    which containers surround the reference.
    """
    def visit(node):
        if node.name in _CONSTRUCTORS:
            return SourceType(node.name, tuple(visit(child) for child in node.arguments))
        return SourceType(rename_atom(node.name), nullable=node.nullable)

    return render_type(visit(parse_type(typ)))


def type_children(typ: str) -> Tuple[str, ...]:
    """Return immediate type arguments; scalar and nullable class leaves have none."""
    return tuple(render_type(child) for child in parse_type(typ).arguments)


def tuple_elements(typ: str) -> Optional[Tuple[str, ...]]:
    """Return a tuple's component types, including ``()`` for an empty tuple."""
    node = parse_type(typ)
    return type_children(typ) if node.name == "Tuple" else None


def make_tuple_type(elements: Iterable[str]) -> str:
    """Build a fixed-arity tuple type without flattening nested tuples."""
    return render_type(SourceType("Tuple", tuple(parse_type(element) for element in elements)))


def contains_reference(typ: str) -> bool:
    """Whether values can contain a shared object or mutable collection reference."""
    def visit(node):
        if node.name == "Tuple":
            return any(visit(child) for child in node.arguments)
        return node.name not in _PRIMITIVES

    return visit(parse_type(typ))


def supports_equality(typ: str) -> bool:
    """Whether source equality is available structurally, before feature gating.

    Class equality compares identities. Collections retain their existing lack
    of source equality. Real equality is mathematical, and does not promise an
    executable decision procedure.
    """
    def visit(node):
        if node.name == "Tuple":
            return all(visit(child) for child in node.arguments)
        return node.name not in {"Seq", "Set", "Dict"}

    return visit(parse_type(typ))


def supports_key(typ: str, *, allow_real: bool = False) -> bool:
    """Whether a type has stable key equality, independent of mutable contents.

    Object references are identity keys, including nullable references. Real
    keys require an explicit opt-in by the feature layer. Abstract interfaces
    require a separate check with the frontend's class declaration context.
    """
    def visit(node):
        if node.name == "Tuple":
            return all(visit(child) for child in node.arguments)
        return node.name not in {"Seq", "Set", "Dict"} and (allow_real or node.name != "Real")

    return visit(parse_type(typ))


def sequence_element(typ: str) -> Optional[str]:
    """Return a sequence's canonical element type, or None for other types."""
    # Preserve the existing predicate's handling of arbitrary non-sequence names.
    if typ != "Seq" and not typ.startswith("Seq["):
        return None
    node = parse_type(typ)
    return render_type(node.arguments[0]) if node.name == "Seq" else None


def sequence_type(element: str) -> str:
    """Build a canonical sequence type, spelling integer sequences as bare Seq."""
    return render_type(SourceType("Seq", (parse_type(element),)))


def is_sequence(typ: str) -> bool:
    return sequence_element(typ) is not None


def is_finite_collection(typ: str) -> bool:
    return typ.startswith(("Set[", "Dict[")) and parse_type(typ).name in {"Set", "Dict"}


def is_dictionary(typ: str) -> bool:
    return typ.startswith("Dict[") and parse_type(typ).name == "Dict"


def dictionary_types(typ: str) -> Optional[Tuple[str, str]]:
    return type_children(typ) if is_dictionary(typ) else None


def is_collection(typ: str) -> bool:
    """Whether the type uses the generic mutable collection representation.

    Integer sequences retain their dedicated heap store. Other sequences, sets,
    and dictionaries use typed collections; tuples remain immutable values.
    """
    if is_sequence(typ):
        return sequence_element(typ) != "Int"
    return is_finite_collection(typ)


def collection_element(typ: str) -> Optional[str]:
    """Return the element of a typed sequence or set; dictionaries have two types."""
    if is_collection(typ):
        node = parse_type(typ)
        if node.name in {"Seq", "Set"}:
            return render_type(node.arguments[0])
    return None
