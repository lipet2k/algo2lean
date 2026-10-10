"""Command-line entry point: python3 -m algo2lean."""

import argparse
import ast
import math
from pathlib import Path
import sys

from .checker import check_lean
from .compiler import CompileError, compile_source
from .modules import generated_module_name, validate_module_name
from .publication import PublicationError


def same_path(first: Path, second: Path) -> bool:
    """Recognize lexical paths, symlinks, and existing hard-link aliases."""
    return first.resolve() == second.resolve() or (
        first.exists() and second.exists() and first.samefile(second))


def write_if_changed(path: Path, contents: str) -> None:
    """Write changed text only, preserving the timestamps of identical outputs."""
    if path.exists() and path.read_bytes() == contents.encode("utf-8"):
        return
    path.write_text(contents, encoding="utf-8")


def has_project_imports(source: str) -> bool:
    """Detect declaration imports without executing source or hiding diagnostics."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return False  # The selected compiler supplies the normal source error.
    return any(isinstance(node, (ast.Import, ast.ImportFrom)) for node in tree.body)


def project_outputs(compilation, directory: Path):
    """Preflight all canonical outputs before creating or replacing any file."""
    root = directory.expanduser().resolve()
    protected = [Path(__file__).resolve().parent.parent / "Algo2Lean.lean"]
    for module in compilation.project.modules.values():
        protected += [module.path, module.path.with_suffix(".lean"),
                      compilation.project.root / "analysis" / module.path.relative_to(compilation.project.root).with_suffix(".lean")]
    markers = {
        "Generated": "-- Independently compiled module; imported algorithms keep their own transitions.",
        "Points": "-- Named locations are independent of the compiled module body.",
        "Facts": "-- Optional proof certificate; execution remains the generated Step relation.",
    }
    outputs = []
    for name, contents in compilation.files.items():
        parts = name.split(".")
        if parts[0] != "Algo" or parts[-1] not in markers:
            raise ValueError("Unexpected generated project module '%s'." % name)
        output = root.joinpath(*parts).with_suffix(".lean")
        if not output.resolve().is_relative_to(root):
            raise ValueError("Generated output '%s' escapes the output directory through a symbolic link." % output)
        parent = output
        while parent != root:
            if parent.is_symlink():
                raise ValueError("Generated output paths must not use symbolic links: %s." % parent)
            parent = parent.parent
        if any(same_path(output, path) for path in protected):
            raise ValueError("Generated output would overwrite source, analysis, or shared library: %s." % output)
        if output.exists():
            if not output.is_file() or output.stat().st_nlink > 1:
                raise ValueError("Generated output must be an ordinary unaliased file: %s." % output)
            existing = output.read_text(encoding="utf-8")
            if existing != contents and markers[parts[-1]] not in existing.splitlines():
                raise ValueError("Refusing to overwrite an existing source or proof file: %s." % output)
        outputs.append((output, contents))
    return outputs


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description="Compile mathematical algorithms to Lean 4 output relations.")
    commands = parser.add_subparsers(dest="command", required=True)
    compile_parser = commands.add_parser("compile", help="Compile an .algo source file to Lean 4.")
    compile_parser.add_argument("source", type=Path)
    compile_parser.add_argument("-o", "--output", type=Path, help="Write core Lean to Foo.lean and named points to FooPoints.lean (default: core on standard output).")
    compile_parser.add_argument("--points-output", type=Path, help="Named-points output path; must be <core module>Points.lean, beside -o when given. With standard output, the core module is derived from the source filename.")
    compile_parser.add_argument("--check", action="store_true", help="Ask Lean to check the generated definitions before writing them.")
    compile_parser.add_argument("--standalone", action="store_true", help="Embed the shared Lean library instead of importing Algo2Lean.")
    compile_parser.add_argument("--project", type=Path, help="Resolve .algo imports beneath this explicit project root.")
    compile_parser.add_argument("--output-dir", type=Path, help="Export a project as Algo/<module>/Generated.lean, Points.lean, and Facts.lean.")
    verify_parser = commands.add_parser("verify", help="Regenerate a source and compare exact generated Lean files in a folder.")
    verify_parser.add_argument("source", type=Path)
    verify_parser.add_argument("generated", type=Path, help="Folder containing claimed generated files at their original relative paths.")
    verify_parser.add_argument("--project", type=Path, help="Resolve imported source files beneath this project root.")
    verify_parser.add_argument("--standalone", action="store_true", help="Compare output with the shared library embedded.")
    analyze_parser = commands.add_parser("analyze", help="Check a separate Lean analysis importing the compiled algorithm.")
    analyze_parser.add_argument("source", type=Path)
    analyze_parser.add_argument("analysis", type=Path)
    analyze_parser.add_argument("--timeout", type=float, default=120, help="Checking time limit in seconds (default: 120).")
    analyze_parser.add_argument("--project", type=Path, help="Resolve .algo imports and companion Lean analyses beneath this project root.")
    library_parser = commands.add_parser("library", help="Export the reusable Algo2Lean.lean library.")
    library_parser.add_argument("-o", "--output", type=Path, help="Write the library to this file (default: standard output).")
    serve_parser = commands.add_parser("serve", help="Start the local browser editor.")
    serve_parser.add_argument("--port", type=int, default=8765)
    serve_parser.add_argument("--open", action="store_true", help="Open the editor in your default browser.")
    args = parser.parse_args(argv)
    if args.command == "verify":
        from .verification import verify_generated
        try:
            project_root = args.project
            if project_root is None and has_project_imports(args.source.read_text(encoding="utf-8")):
                project_root = args.source.resolve().parent
            result = verify_generated(args.source, args.generated,
                                      project_root=project_root, standalone=args.standalone)
            if result["exact"]:
                print("Exact match: %d generated and supplied library files match this compiler's output." % result["compared"])
            else:
                print("Files do not exactly match this compilation.")
                for key, label in (("missing", "Missing"), ("extra", "Extra"), ("different", "Different contents")):
                    for name in result[key]:
                        print(label + ": " + name)
            print("Generation verification does not check a Lean proof or prove compiler correctness.")
            return 0 if result["exact"] else 1
        except (OSError, UnicodeError, CompileError, ValueError) as error:
            print(str(error), file=sys.stderr)
            return 1
    if args.command == "analyze":
        from .analysis import check_analysis
        if not math.isfinite(args.timeout) or args.timeout <= 0:
            parser.error("--timeout must be positive")
        try:
            source = args.source.read_text(encoding="utf-8")
            analysis = args.analysis.read_text(encoding="utf-8")
            if args.project is not None or has_project_imports(source):
                from .modular import compile_project
                from .project_checker import check_project
                generated = compile_project(args.source.resolve(), root=args.project or args.source.resolve().parent)
                checked = check_project(generated, analysis=analysis, timeout=args.timeout)
            else:
                generated = compile_source(source, filename=str(args.source))
                checked = check_analysis(generated.lean, analysis,
                                         generated.module, timeout=args.timeout, points_lean=generated.points_lean)
            print(checked.output)
            return 0 if checked.ok else 1
        except PublicationError as error:
            print("Compiler setup error: %s" % error, file=sys.stderr)
            return 1
        except (OSError, UnicodeError, CompileError) as error:
            print(str(error), file=sys.stderr)
            return 1
    if args.command == "library":
        try:
            library = (Path(__file__).resolve().parent.parent / "Algo2Lean.lean").read_text(encoding="utf-8")
            if args.output:
                args.output.write_text(library, encoding="utf-8")
                print("Wrote %s" % args.output, file=sys.stderr)
            else:
                sys.stdout.write(library)
            return 0
        except (OSError, UnicodeError) as error:
            print("Could not export the shared library: %s" % error, file=sys.stderr)
            return 1
    if args.command == "serve":
        from .server import serve
        try:
            serve(args.port, args.open)
        except (OSError, ValueError) as error:
            print("Could not start the editor: %s" % error, file=sys.stderr)
            return 1
        return 0
    try:
        source = args.source.read_text(encoding="utf-8")
        if args.project is not None or args.output_dir is not None or has_project_imports(source):
            from .modular import compile_project
            from .project_checker import check_project
            if args.output is not None or args.points_output is not None or args.standalone:
                raise ValueError("Project compilation does not support -o, --points-output, or --standalone; use --output-dir instead.")
            result = compile_project(args.source.resolve(), root=args.project or args.source.resolve().parent)
            outputs = project_outputs(result, args.output_dir) if args.output_dir is not None else []
            if args.check:
                checked = check_project(result, check_facts=False)
                print(checked.output, file=sys.stderr)
                if not checked.ok:
                    return 1
            if args.output_dir is not None:
                for output, contents in outputs:
                    output.parent.mkdir(parents=True, exist_ok=True)
                    write_if_changed(output, contents)
                    print("Wrote %s" % output, file=sys.stderr)
            else:
                sys.stdout.write(result.entry.lean)
                print("Use --output-dir DIR to export the canonical module files and their dependencies.", file=sys.stderr)
            return 0
        module = generated_module_name(args.source.name)
        if args.output:
            if args.output.suffix != ".lean":
                raise ValueError("The core output filename must end in .lean.")
            module = validate_module_name(args.output.stem)
        points_output = args.points_output
        if args.output and points_output is None:
            points_output = args.output.with_name(module + "Points.lean")
        if points_output:
            if points_output.name != module + "Points.lean":
                raise ValueError("The named-points output must be named %sPoints.lean." % module)
            if args.output and points_output.parent.resolve() != args.output.parent.resolve():
                raise ValueError("The core and named-points output files must be in the same directory.")
        library_path = Path(__file__).resolve().parent.parent / "Algo2Lean.lean"
        for output in (args.output, points_output):
            if output is None:
                continue
            if same_path(output, args.source):
                raise ValueError("Choose output paths different from the source file.")
            if output.name.casefold() == "algo2lean.lean" or same_path(output, library_path):
                raise ValueError("Algo2Lean.lean is reserved for the shared library. Choose another output filename.")
        if args.output and points_output and same_path(args.output, points_output):
            raise ValueError("Choose different paths for the core and named-points output files.")
        result = compile_source(source, filename=str(args.source), standalone=args.standalone, module=module)
        if args.check:
            checked = check_lean(result.lean, module=result.module, points_lean=result.points_lean)
            print(checked.output, file=sys.stderr)
            if not checked.ok:
                return 1
        if args.output:
            write_if_changed(args.output, result.lean)
            print("Wrote %s" % args.output, file=sys.stderr)
        else:
            sys.stdout.write(result.lean)
        if points_output:
            write_if_changed(points_output, result.points_lean)
            print("Wrote %s" % points_output, file=sys.stderr)
            if args.output is None:
                print("Save the core standard output as %s.lean beside it." % module, file=sys.stderr)
        return 0
    except PublicationError as error:
        print("Compiler setup error: %s" % error, file=sys.stderr)
    except CompileError as error:
        print("%s:%s:%s: %s" % (getattr(error, "file", args.source), error.line, error.column, error.message), file=sys.stderr)
    except (OSError, UnicodeError) as error:
        print("Could not read or write the file: %s" % error, file=sys.stderr)
    except ValueError as error:
        print(str(error), file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
