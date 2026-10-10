"""Static, root-confined resolution of declaration-only ``.algo`` modules.

A dotted module ``pkg.sorting`` means ``<root>/pkg/sorting.algo``.  There are
no Python packages, import hooks, implicit ``__init__`` files, or source
execution.  Imports bind existing symbols; aliases never change their identity.
"""

import ast
import keyword
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Mapping, Optional, Tuple, Union

from .frontend import BUILTINS, TYPES, CompileError
from .source_validation import RESOURCE_LIMIT, parse_source


_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*\Z")


class ProjectError(CompileError):
    """An input diagnostic that also identifies the file in a project."""

    def __init__(self, message: str, path: Path, line: int = 1, column: int = 1):
        super().__init__(message, line, column)
        self.path = str(path)
        self.file = self.path

    def __str__(self) -> str:
        return "%s:%s:%s: %s" % (self.path, self.line, self.column, self.message)

    def to_dict(self):
        return dict(super().to_dict(), file=self.file)


@dataclass(frozen=True)
class Symbol:
    """The declaration's identity, independent of local import spelling."""

    module: str
    name: str
    kind: str

    @property
    def canonical_name(self) -> str:
        return self.module + ("." + self.name if self.name else "")


INTERFACE = Symbol("algo2lean", "Interface", "builtin")


@dataclass
class SourceModule:
    name: str
    path: Path
    source: str
    tree: ast.Module
    dependencies: Tuple[str, ...] = ()
    bindings: Dict[str, Symbol] = field(default_factory=dict)
    exports: Dict[str, Symbol] = field(default_factory=dict)
    resolved_symbols: Dict[int, Symbol] = field(default_factory=dict)
    # Quoted annotations are parsed, never evaluated. Their separate trees keep
    # the source tree intact and give lowering the same symbol map as bare types.
    quoted_annotations: Dict[int, ast.expr] = field(default_factory=dict)


@dataclass
class Project:
    root: Path
    entry: str
    # Dependencies precede callers except within a mutually dependent group.
    modules: Dict[str, SourceModule] = field(default_factory=dict)
    # Retain unvisited editor buffers for algorithm dependencies mentioned only
    # by a subsequently selected Lean analysis. Keys are root-relative .algo
    # paths: a canonical module like pkg.algo is otherwise ambiguous with the
    # filename pkg.algo when passed back through the public loader.
    source_overlays: Dict[str, str] = field(default_factory=dict)
    # Each group is compiled together. Members are sorted so the identity of a
    # recursive group does not depend on which of its modules was the entry.
    compilation_groups: Tuple[Tuple[str, ...], ...] = ()

    def transitive_dependencies(self, module: Union[str, SourceModule]) -> Tuple[str, ...]:
        owner = self.modules[module] if isinstance(module, str) else module
        seen = {owner.name}
        ordered = []

        def visit(name):
            if name in seen:
                return
            seen.add(name)
            for dependency in self.modules[name].dependencies:
                visit(dependency)
            ordered.append(name)

        for dependency in owner.dependencies:
            visit(dependency)
        return tuple(ordered)

    def resolve(self, module: Union[str, SourceModule], reference: Union[str, ast.AST]) -> Optional[Symbol]:
        """Resolve a bare or dotted static name; return None for object fields.

        This is lexical module lookup. ``resolved_symbols`` additionally accounts
        for function-local shadowing. A caller may parse a quoted annotation and
        resolve its names here without modifying or evaluating the source.
        """
        owner = self.modules[module] if isinstance(module, str) else module
        parts = _reference_parts(reference)
        if not parts:
            return None
        symbol = owner.bindings.get(parts[0])
        reachable = set(self.transitive_dependencies(owner)) | {owner.name}
        for part in parts[1:]:
            if symbol is None or symbol.kind != "module":
                return None
            if symbol.module == "algo2lean":
                symbol = INTERFACE if part == "Interface" else None
                continue
            imported = owner if symbol.module == owner.name else self.modules.get(symbol.module)
            exported = imported.exports.get(part) if imported and symbol.module in reachable else None
            child = symbol.module + "." + part
            if exported is not None:
                symbol = exported
            elif any(name == child or name.startswith(child + ".") for name in reachable):
                symbol = Symbol(child, "", "module")
            else:
                return None
        return symbol


def _reference_parts(reference):
    if isinstance(reference, str):
        return reference.split(".") if _valid_module(reference) else None
    if isinstance(reference, ast.Name):
        return [reference.id]
    if isinstance(reference, ast.Attribute):
        prefix = _reference_parts(reference.value)
        return prefix + [reference.attr] if prefix else None
    return None


def _valid_module(name):
    return isinstance(name, str) and bool(name) and all(
        _NAME.fullmatch(part) and not keyword.iskeyword(part) for part in name.split("."))


def _error(path, node, message):
    raise ProjectError(message, path, getattr(node, "lineno", 1), getattr(node, "col_offset", 0) + 1)


class _Loader:
    def __init__(self, root, sources, max_modules):
        self.root = Path(root).expanduser().resolve()
        self.project = Project(self.root, "")
        self.sources = {}
        self.spellings = {}
        self.loading = []
        self.paths = {}
        self.pending_imports = []
        self.max_modules = max_modules
        for key, source in (sources or {}).items():
            name = self.module_name(key)
            if name in self.sources:
                raise ProjectError("Duplicate in-memory source for '%s'." % name, self.path(name))
            if not isinstance(source, str):
                raise ProjectError("Module sources must be text.", self.path(name))
            self._register_spelling(name, self.path(name), None)
            self.sources[name] = source
        self.project.source_overlays = {
            self.path(name).relative_to(self.root).as_posix(): source
            for name, source in self.sources.items()
        }

    def module_name(self, value):
        text = str(value)
        if _valid_module(text) and not text.endswith(".algo"):
            return text
        candidate = Path(value).expanduser()
        if not candidate.is_absolute():
            candidate = self.root / candidate
        # Check the lexical path as well: accepting ../root/file obscures the
        # project boundary and would make virtual-source keys ambiguous.
        if ".." in candidate.parts:
            raise ProjectError("Module paths must stay inside the project root.", candidate)
        try:
            relative = candidate.relative_to(self.root)
        except ValueError:
            raise ProjectError("Module paths must stay inside the project root.", candidate) from None
        if relative.suffix != ".algo":
            raise ProjectError("A source path must end in .algo.", candidate)
        parts = relative.with_suffix("").parts
        if not all(_NAME.fullmatch(part) and not keyword.iskeyword(part) for part in parts):
            raise ProjectError("Module names must use ASCII identifiers separated by dots.", candidate)
        return ".".join(parts)

    def path(self, name):
        return self.root.joinpath(*name.split(".")).with_suffix(".algo")

    def _register_spelling(self, name, path, node):
        parts = name.split(".")
        for end in range(1, len(parts) + 1):
            prefix = ".".join(parts[:end])
            old = self.spellings.get(prefix.casefold())
            if old is not None and old != prefix:
                _error(path, node, "Case-colliding module names '%s' and '%s'." % (old, prefix))
            self.spellings[prefix.casefold()] = prefix

    def _safe_path(self, name, diagnostic_path, node):
        candidate = self.path(name)
        try:
            real = candidate.resolve()
        except (OSError, RuntimeError):
            _error(diagnostic_path, node, "Cannot resolve module path for '%s'." % name)
        if not real.is_relative_to(self.root):
            _error(diagnostic_path, node, "Module '%s' escapes the project root through a symbolic link." % name)
        parent = self.root
        for segment in candidate.relative_to(self.root).parts:
            try:
                matches = [item.name for item in parent.iterdir() if item.name.casefold() == segment.casefold()]
            except FileNotFoundError:
                break  # The rest may be supplied by the editor's source mapping.
            except OSError as exc:
                _error(diagnostic_path, node, "Cannot inspect module path: %s." % exc.strerror)
            if len(matches) > 1:
                _error(diagnostic_path, node, "Case-colliding filesystem entries for '%s'." % segment)
            if matches and matches[0] != segment:
                _error(diagnostic_path, node, "Module path case mismatch: requested '%s', found '%s'." % (segment, matches[0]))
            parent /= segment
        previous = self.paths.get(real)
        if previous is not None and previous != name:
            _error(diagnostic_path, node, "Modules '%s' and '%s' refer to the same source path." % (previous, name))
        self.paths[real] = name
        return candidate

    def load(self, name, importer=None, node=None):
        origin = importer.path if importer else self.path(name)
        if not _valid_module(name):
            _error(origin, node, "Module names must use ASCII identifiers separated by dots.")
        if name == "algo2lean" or name.startswith("algo2lean."):
            _error(origin, node, "'algo2lean' is reserved for compiler-provided declarations.")
        if name.split(".")[0].casefold() == "_a2l_groups":
            _error(origin, node, "'_a2l_groups' is reserved for generated recursive compilation groups.")
        self._register_spelling(name, origin, node)
        if name in self.project.modules:
            return self.project.modules[name]
        if len(self.project.modules) >= self.max_modules:
            _error(origin, node, "Project exceeds the limit of %s modules." % self.max_modules)
        path = self._safe_path(name, origin, node)
        try:
            source = self.sources[name] if name in self.sources else path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as exc:
            message = "Module '%s' was not found at %s." % (name, path) if isinstance(exc, FileNotFoundError) else "Cannot read module '%s': %s." % (name, exc)
            _error(origin, node, message)
        try:
            tree = parse_source(source, path)
        except CompileError as exc:
            raise ProjectError(exc.message, path, exc.line, exc.column) from None
        module = SourceModule(name, path, source, tree)
        self.loading.append(name)
        self._declarations(module)
        # Register declarations before following imports. Sources contain no
        # executable top-level statements, so recursive imports need no Python
        # module-initialization order and can share these declaration identities.
        module.exports = dict(module.bindings)
        self.project.modules[name] = module
        dependencies = []
        for declaration in tree.body:
            if not isinstance(declaration, (ast.Import, ast.ImportFrom)):
                continue
            if isinstance(declaration, ast.Import):
                for alias in declaration.names:
                    if alias.name == "algo2lean":
                        imported_name = "algo2lean"
                    else:
                        imported_name = self.load(alias.name, module, declaration).name
                        dependencies.append(imported_name)
                    local = alias.asname or imported_name.split(".")[0]
                    symbol = Symbol(imported_name if alias.asname else imported_name.split(".")[0], "", "module")
                    self._bind(module, local, symbol, declaration)
            else:
                if declaration.level:
                    _error(path, declaration, "Relative imports are not supported.")
                if any(alias.name == "*" for alias in declaration.names):
                    _error(path, declaration, "Wildcard imports are not supported.")
                if declaration.module == "algo2lean":
                    exports = {"Interface": INTERFACE}
                    for alias in declaration.names:
                        if alias.name not in exports:
                            _error(path, declaration, "Module 'algo2lean' does not export '%s'." % alias.name)
                        self._bind(module, alias.asname or alias.name, exports[alias.name], declaration)
                else:
                    imported = self.load(declaration.module, module, declaration)
                    dependencies.append(imported.name)
                    for alias in declaration.names:
                        self.pending_imports.append((module, declaration, alias))
        module.dependencies = tuple(dict.fromkeys(dependencies))
        self.loading.pop()
        return module

    def finish(self):
        """Resolve the complete declaration graph before inspecting bodies."""
        pending = self.pending_imports
        while pending:
            unresolved = []
            for module, declaration, alias in pending:
                exports = self.project.modules[declaration.module].exports
                if alias.name in exports:
                    self._bind(module, alias.asname or alias.name, exports[alias.name], declaration)
                else:
                    unresolved.append((module, declaration, alias))
            if len(unresolved) == len(pending):
                self._unresolved_import(unresolved)
            pending = unresolved

        # Imported aliases must retain the declaration's final kind as well as
        # its identity. Classifying after name resolution also handles Interface
        # markers re-exported through a mutually dependent group of modules.
        interfaces = {}
        for module in self.project.modules.values():
            for declaration in module.tree.body:
                if isinstance(declaration, ast.ClassDef) and (declaration.bases or declaration.keywords):
                    if declaration.keywords or len(declaration.bases) != 1 or self.project.resolve(module, declaration.bases[0]) != INTERFACE:
                        _error(module.path, declaration, "Class inheritance is unsupported; interfaces must use the imported Interface marker as their only base.")
                    old = module.bindings[declaration.name]
                    interfaces[old] = Symbol(module.name, declaration.name, "interface")
        for module in self.project.modules.values():
            module.bindings = {name: interfaces.get(symbol, symbol) for name, symbol in module.bindings.items()}
            module.exports = dict(module.bindings)

        self.project.compilation_groups = _compilation_groups(self.project.modules)
        self.project.modules = {
            name: self.project.modules[name]
            for group in self.project.compilation_groups for name in group
        }
        for module in self.project.modules.values():
            self.loading.append(module.name)
            _References(self.project, module).visit(module.tree)
            self.loading.pop()

    def _unresolved_import(self, pending):
        """Explain an ungrounded alias cycle or its missing export endpoint."""
        imports = {
            (module.name, alias.asname or alias.name): (module, declaration, alias)
            for module, declaration, alias in pending
        }
        module, declaration, alias = pending[0]
        chain = []
        positions = {}
        while True:
            key = (module.name, alias.asname or alias.name)
            if key in positions:
                cycle = chain[positions[key]:] + [key]
                _error(module.path, declaration,
                       "Unresolved cyclic re-export: %s. The imported name needs a function, class, or module declaration."
                       % " -> ".join(owner + "." + name for owner, name in cycle))
            positions[key] = len(chain)
            chain.append(key)
            target = (declaration.module, alias.name)
            if target not in imports:
                _error(module.path, declaration, "Module '%s' does not export '%s'." % target)
            module, declaration, alias = imports[target]

    def _bind(self, module, local, symbol, node):
        if not _NAME.fullmatch(local) or local in TYPES or local in BUILTINS:
            _error(module.path, node, "Import or definition name '%s' is reserved or invalid." % local)
        previous = module.bindings.get(local)
        if previous is not None and previous != symbol:
            _error(module.path, node, "Conflicting binding for '%s'." % local)
        module.bindings[local] = symbol
        module.exports[local] = symbol

    def _declarations(self, module):
        top_imports = {id(node) for node in module.tree.body if isinstance(node, (ast.Import, ast.ImportFrom))}
        for node in ast.walk(module.tree):
            if isinstance(node, (ast.Import, ast.ImportFrom)) and id(node) not in top_imports:
                _error(module.path, node, "Imports must be unconditional module-level declarations.")
        declarations = set()
        for node in module.tree.body:
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                continue
            if not isinstance(node, (ast.FunctionDef, ast.ClassDef)):
                _error(module.path, node, "Only imports, function definitions, and class definitions are allowed at the top level.")
            if node.name in declarations:
                _error(module.path, node, "Duplicate definition '%s'." % node.name)
            declarations.add(node.name)
            self._bind(module, node.name, Symbol(module.name, node.name, "function" if isinstance(node, ast.FunctionDef) else "class"), node)


def _compilation_groups(modules):
    """Tarjan components in dependency-first order, retaining acyclic ordering."""
    indices = {}
    lowlinks = {}
    stack = []
    active = set()
    groups = []

    def visit(name):
        indices[name] = lowlinks[name] = len(indices)
        stack.append(name)
        active.add(name)
        for dependency in modules[name].dependencies:
            if dependency not in indices:
                visit(dependency)
                lowlinks[name] = min(lowlinks[name], lowlinks[dependency])
            elif dependency in active:
                lowlinks[name] = min(lowlinks[name], indices[dependency])
        if lowlinks[name] == indices[name]:
            members = []
            while True:
                member = stack.pop()
                active.remove(member)
                members.append(member)
                if member == name:
                    break
            groups.append(tuple(sorted(members)))

    for name in modules:
        if name not in indices:
            visit(name)
    return tuple(groups)


class _References(ast.NodeVisitor):
    """Record static references without confusing parameters with module aliases."""

    def __init__(self, project, module):
        self.project = project
        self.module = module
        self.locals = set()
        self.declarations = {id(node) for node in module.tree.body}

    def _record(self, node):
        parts = _reference_parts(node)
        if parts and parts[0] not in self.locals:
            symbol = self.project.resolve(self.module, node)
            if symbol is not None:
                self.module.resolved_symbols[id(node)] = symbol
            elif isinstance(node, ast.Attribute):
                namespace = self.project.resolve(self.module, node.value)
                if namespace is not None and namespace.kind == "module":
                    _error(self.module.path, node, "Module '%s' does not export '%s'." % (namespace.module, node.attr))

    def visit_Name(self, node):
        if isinstance(node.ctx, ast.Load):
            self._record(node)

    def visit_Attribute(self, node):
        if isinstance(node.ctx, ast.Load):
            self._record(node)
        self.generic_visit(node)

    def annotation(self, node):
        if node is None:
            return
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            try:
                parsed = ast.parse(node.value, mode="eval").body
            except (SyntaxError, ValueError):
                _error(self.module.path, node, "Invalid quoted type annotation.")
            for part in ast.walk(parsed):
                ast.copy_location(part, node)
            self.module.quoted_annotations[id(node)] = parsed
            self.visit(parsed)
        else:
            self.visit(node)

    def visit_FunctionDef(self, node):
        if id(node) in self.declarations:
            self.module.resolved_symbols[id(node)] = self.module.bindings[node.name]
        # Annotations live in module scope, even when a parameter has the same
        # spelling as the annotation's imported class.
        outer = self.locals
        self.locals = set()
        for argument in node.args.posonlyargs + node.args.args + node.args.kwonlyargs:
            self.annotation(argument.annotation)
        self.annotation(node.returns)
        self.locals = outer
        for default in node.args.defaults + [value for value in node.args.kw_defaults if value is not None]:
            self.visit(default)
        for decorator in node.decorator_list:
            self.visit(decorator)
        local_names = {argument.arg for argument in node.args.posonlyargs + node.args.args + node.args.kwonlyargs}
        local_names.update(argument.arg for argument in (node.args.vararg, node.args.kwarg) if argument)
        local_names.update(part.id for statement in node.body for part in ast.walk(statement)
                           if isinstance(part, ast.Name) and isinstance(part.ctx, (ast.Store, ast.Del)))
        self.locals = outer | local_names
        for statement in node.body:
            self.visit(statement)
        self.locals = outer

    def visit_ClassDef(self, node):
        if id(node) in self.declarations:
            self.module.resolved_symbols[id(node)] = self.module.bindings[node.name]
        for base in node.bases:
            self.visit(base)
        for member in node.body:
            self.visit(member)

    def visit_AnnAssign(self, node):
        self.visit(node.target)
        outer = self.locals
        self.locals = set()
        self.annotation(node.annotation)
        self.locals = outer
        if node.value is not None:
            self.visit(node.value)


def load_project(entry: Union[str, Path], *, root: Union[str, Path],
                 sources: Optional[Mapping[str, str]] = None, max_modules: int = 256) -> Project:
    """Read a module and its import graph without executing Python.

    ``entry`` is a dotted module name or a root-contained ``.algo`` path.
    ``sources`` overlays disk files by dotted name or root-contained file path,
    so an editor can resolve unsaved buffers with the same rules as the build.
    Every file access remains under the explicit root, including symlinks.
    """
    if not isinstance(max_modules, int) or max_modules < 1:
        raise ValueError("max_modules must be a positive integer")
    loader = _Loader(root, sources, max_modules)
    loader.project.entry = loader.module_name(entry)
    try:
        loader.load(loader.project.entry)
        loader.finish()
    except (RecursionError, MemoryError):
        owner = loader.loading[-1] if loader.loading else loader.project.entry
        raise ProjectError(RESOURCE_LIMIT, loader.path(owner)) from None
    return loader.project
