"""Bounded exact decimal parsing, independent of Python floating-point values."""

from math import gcd
import re


MAX_LITERAL_CHARACTERS = 1024
MAX_EXPONENT_MAGNITUDE = 1024
MAX_EXPANDED_DIGITS = 2048
_DIGITS = r"[0-9](?:_?[0-9])*"
_LITERAL = re.compile(r"(?:" + _DIGITS + r"(?:\.(?:" + _DIGITS + r")?)?|\." +
                      _DIGITS + r")(?:[eE][+-]?" + _DIGITS + r")?\Z")


class RealLiteralError(ValueError):
    """A decimal spelling or its exact representation exceeds the source rules."""


def parse_real_literal(token):
    """Return the reduced exact ratio of a decimal/scientific source token.

    Signs belong to unary expressions, not literal tokens. Limits apply before
    creating large powers or integer values. An overflowing or underflowing
    Python float is irrelevant: only the bounded source spelling is interpreted.
    """
    if not isinstance(token, str):
        raise RealLiteralError("An exact real literal requires its source token.")
    if len(token) > MAX_LITERAL_CHARACTERS:
        raise RealLiteralError("Real literal exceeds the %d character limit." % MAX_LITERAL_CHARACTERS)
    if not _LITERAL.fullmatch(token) or not any(marker in token for marker in ".eE"):
        raise RealLiteralError("Expected a decimal or scientific real literal.")
    spelling = token.replace("_", "").lower()
    mantissa, marker, exponent_text = spelling.partition("e")
    exponent = int(exponent_text) if marker else 0
    if abs(exponent) > MAX_EXPONENT_MAGNITUDE:
        raise RealLiteralError("Real literal exponent magnitude exceeds %d." % MAX_EXPONENT_MAGNITUDE)
    whole, point, fraction = mantissa.partition(".")
    digits = (whole + fraction).lstrip("0") or "0"
    shift = exponent - len(fraction)
    numerator_digits = len(digits) + max(shift, 0)
    denominator_digits = 1 + max(-shift, 0)
    if max(numerator_digits, denominator_digits) > MAX_EXPANDED_DIGITS:
        raise RealLiteralError("Real literal expands beyond %d decimal digits." % MAX_EXPANDED_DIGITS)
    coefficient = int(digits)
    numerator = coefficient * 10 ** max(shift, 0)
    denominator = 10 ** max(-shift, 0)
    divisor = gcd(numerator, denominator)
    return numerator // divisor, denominator // divisor


def real_literal_ratio(node):
    """Read parser metadata, never reconstruct an exact value from a float."""
    ratio = getattr(node, "exact_ratio", None)
    if (not isinstance(ratio, tuple) or len(ratio) != 2 or
            any(type(value) is not int for value in ratio) or ratio[1] <= 0):
        raise RealLiteralError("Exact real literal metadata is missing; parse the original source text instead of supplying a float AST value.")
    return ratio
