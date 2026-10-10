"""One bounded source parser shared by single files and project modules."""

import ast

from .frontend import CompileError, fail


RESOURCE_LIMIT = "Program nesting or size exceeds the compiler's resource limit."


def parse_source(source, filename="<input>"):
    """Validate text and resource bounds before accepting a source AST."""
    if not isinstance(source, str):
        raise CompileError("Source must be text.")
    if len(source) > 200_000:
        raise CompileError("Source exceeds the 200,000 character limit.")
    for index, character in enumerate(source):
        if character == "\x00" or 0xD800 <= ord(character) <= 0xDFFF:
            line = source.count("\n", 0, index) + 1
            column = index - source.rfind("\n", 0, index)
            raise CompileError("Source contains an invalid text character.", line, column)
    try:
        tree = ast.parse(source, filename=str(filename), mode="exec", type_comments=True)
        if sum(1 for _ in ast.walk(tree)) > 12_000:
            raise CompileError("Program is too large (maximum 12,000 syntax nodes).")
        for node in ast.walk(tree):
            if getattr(node, "type_comment", None):
                fail(node, "Type comments are not supported; use Int, Seq, or Bool annotations.")
        return tree
    except SyntaxError as error:
        raise CompileError(error.msg, error.lineno or 1, error.offset or 1) from None
    except (RecursionError, MemoryError):
        raise CompileError(RESOURCE_LIMIT) from None
