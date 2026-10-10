"""Canonical collection-type parsing shared by the compiler stages.

Bare ``Seq`` is the canonical spelling of integer sequences. Parameterized
sequences retain their element type, including nested collections. Centralizing
these rules lets collection types evolve without duplicating parsing logic
or changing how compiler stages identify class names.
"""

from typing import Optional


def sequence_element(typ: str) -> Optional[str]:
    """Return a canonical sequence's element type, or None for other types."""
    if typ == "Seq":
        return "Int"
    if typ.startswith("Seq[") and typ.endswith("]"):
        return typ[4:-1]
    return None


def sequence_type(element: str) -> str:
    """Build a canonical sequence type, spelling integer sequences as bare Seq."""
    return "Seq" if element == "Int" else "Seq[%s]" % element


def is_sequence(typ: str) -> bool:
    return sequence_element(typ) is not None


def is_collection(typ: str) -> bool:
    """Whether the type uses the generic collection representation.

    Integer sequences use a dedicated heap store; other sequences use typed collections.
    """
    return typ != "Seq" and is_sequence(typ)


def collection_element(typ: str) -> Optional[str]:
    return sequence_element(typ) if is_collection(typ) else None
