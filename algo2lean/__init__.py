"""Algo2Lean: mathematical algorithms as Lean 4 output relations."""

from .compiler import CompilationResult, CompileError, compile_source
from .modules import generated_module_name

__all__ = ["CompilationResult", "CompileError", "compile_source", "generated_module_name"]
