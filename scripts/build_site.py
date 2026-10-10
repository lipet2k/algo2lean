"""Build a self-contained, versioned static compiler site without development history."""

import argparse
import hashlib
import html
import io
import json
from pathlib import Path
import re
import shutil
import tarfile
import tempfile
from urllib.request import urlopen
import zipfile


ROOT = Path(__file__).resolve().parents[1]
RUNTIME_FILES = (
    "pyodide.mjs", "pyodide.asm.mjs", "pyodide.asm.wasm",
    "python_stdlib.zip", "pyodide-lock.json",
)


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def snapshot(directory):
    result = {}
    for path in sorted(directory.rglob("*")):
        if path.is_symlink():
            raise ValueError("Release assets must not contain symbolic links.")
        if path.is_file():
            result[path.relative_to(directory).as_posix()] = path.read_bytes()
    return result


def zip_bytes(files):
    """Stable archive bytes: ordered names, fixed timestamps and permissions."""
    target = io.BytesIO()
    with zipfile.ZipFile(target, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for name, data in sorted(files.items()):
            info = zipfile.ZipInfo(name, (2020, 1, 1, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            archive.writestr(info, data)
    return target.getvalue()


def compiler_files(root):
    """Only resources used by the compiler and curated editor examples enter WASM."""
    files = {}
    for directory, suffixes in (("algo2lean", {".py"}), ("Algo2LeanLib", {".lean"}),
                                ("examples", {".algo", ".lean"})):
        for path in sorted((root / directory).rglob("*")):
            if path.is_file() and path.suffix in suffixes and "__pycache__" not in path.parts:
                if path.is_symlink():
                    raise ValueError("Compiler resources must not be symbolic links.")
                files[path.relative_to(root).as_posix()] = path.read_bytes()
    for name in ("Algo2Lean.lean", "publication.json", "lean-toolchain", "LICENSE"):
        files[name] = (root / name).read_bytes()
    return files


def runtime_files(archive, configuration):
    data = Path(archive).read_bytes()
    if digest(data) != configuration["sha256"]:
        raise ValueError("Pyodide archive checksum does not match browser-runtime.json.")
    files = {}
    # Read exact known files; never extract archive-controlled paths to disk.
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:bz2") as bundle:
        for name in RUNTIME_FILES:
            member = bundle.getmember("pyodide/" + name)
            if not member.isfile() or member.size > 40 * 1024 * 1024:
                raise ValueError("Invalid Pyodide runtime asset: " + name)
            files["runtime/" + name] = bundle.extractfile(member).read()
    return files


def release_files(root, runtime, commit=None):
    metadata = json.loads((root / "publication.json").read_text(encoding="utf-8"))
    version = metadata["version"]
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9.+-]*", version):
        raise ValueError("Invalid release version.")
    if commit is not None and not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("Use the complete public Git commit SHA, or omit it for a preview.")
    configuration = json.loads((root / "browser-runtime.json").read_text(encoding="utf-8"))
    payload = compiler_files(root)
    identity = {
        "version": version, "commit": commit,
        "pyodide_version": configuration["version"],
        "bundle_sha256": digest(encoded({name: digest(data) for name, data in payload.items()})),
    }
    payload["release-manifest.json"] = encoded(identity)
    compiler = zip_bytes(payload)
    files = runtime_files(runtime, configuration)
    for path in sorted((root / "editor").iterdir()):
        if path.suffix in {".html", ".js", ".css"}:
            files[path.name] = path.read_bytes()
    page = files["index.html"].decode("utf-8")
    page = page.replace('href="/', 'href="').replace('src="/', 'src="')
    page = page.replace('<script src="app.js" defer>',
                        '<script src="browser-host.js" defer></script>\n  <script src="app.js" defer>')
    files["index.html"] = page.encode("utf-8")
    files["compiler.zip"] = compiler
    files["release-config.json"] = encoded({
        **identity, "compiler_archive": "compiler.zip", "runtime_url": "runtime/",
        "compiler_archive_sha256": digest(compiler), "preview": commit is None,
    })
    for name in ("CITATION.cff", "LICENSE", "THIRD_PARTY_NOTICES.md"):
        files[name] = (root / name).read_bytes()
    for path in sorted((root / "licenses").rglob("*")):
        if path.is_file():
            files[path.relative_to(root).as_posix()] = path.read_bytes()
    files["release-checksums.json"] = encoded({name: digest(data) for name, data in sorted(files.items())})
    return version, files


def verify_release(directory):
    files = snapshot(directory)
    try:
        expected = json.loads(files.pop("release-checksums.json"))
    except (KeyError, ValueError) as error:
        raise ValueError("Archived release has no valid checksums: " + directory.name) from error
    actual = {name: digest(data) for name, data in files.items()}
    if actual != expected:
        raise ValueError("Archived release assets have changed: " + directory.name)


def restore_versions(previous, destination):
    versions = previous / "versions"
    if not versions.is_dir():
        raise ValueError("Previous site must contain a versions directory.")
    for release in sorted(versions.iterdir()):
        if release.is_symlink() or not release.is_dir() or not re.fullmatch(r"v[A-Za-z0-9][A-Za-z0-9.+-]*", release.name):
            raise ValueError("Invalid archived version directory.")
        verify_release(release)
        target = destination / "versions" / release.name
        if target.exists():
            if snapshot(target) != snapshot(release):
                raise ValueError("Conflicting archived release: " + release.name)
        else:
            shutil.copytree(release, target)


def write_site(output, version, files, previous=None):
    output = Path(output)
    if output.is_symlink():
        raise ValueError("Site output must not be a symbolic link.")
    output.mkdir(parents=True, exist_ok=True)
    if previous is not None:
        restore_versions(Path(previous), output)
    target = output / "versions" / ("v" + version)
    if target.exists():
        if snapshot(target) != files:
            raise ValueError("Refusing to change version v%s. Use a new version or a fresh preview directory." % version)
    else:
        target.mkdir(parents=True)
        for name, data in files.items():
            path = target / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
    releases = []
    for path in sorted((output / "versions").iterdir()):
        verify_release(path)
        config = json.loads((path / "release-config.json").read_text(encoding="utf-8"))
        releases.append({**config, "path": "versions/" + path.name + "/"})
    catalog = {"latest": version, "versions": releases}
    (output / "versions.json").write_bytes(encoded(catalog))
    links = "\n".join('<li><a href="%s">Algo2Lean %s%s</a></li>' % (
        html.escape(item["path"]), html.escape(item["version"]),
        " (unpublished preview)" if item["preview"] else "") for item in reversed(releases))
    archive = ('<!doctype html><html lang="en"><meta charset="utf-8">'
               '<meta name="viewport" content="width=device-width, initial-scale=1">'
               '<title>Algo2Lean versions</title><body><main><h1>Algo2Lean versions</h1>'
               '<p>Each version keeps its matching compiler, browser runtime, and Lean libraries.</p>'
               '<ul>' + links + '</ul></main></body></html>\n')
    (output / "versions.html").write_text(archive, encoding="utf-8")
    destination = "versions/v" + version + "/"
    landing = ('<!doctype html><html lang="en"><meta charset="utf-8">'
               '<meta name="viewport" content="width=device-width, initial-scale=1">'
               '<meta http-equiv="refresh" content="0;url=' + html.escape(destination) + '">'
               '<title>Algo2Lean</title><a href="' + html.escape(destination) +
               '">Open Algo2Lean</a> · <a href="versions.html">Earlier versions</a></html>\n')
    (output / "index.html").write_text(landing, encoding="utf-8")
    (output / ".nojekyll").write_text("", encoding="utf-8")
    return target


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "dist/site")
    runtime = parser.add_mutually_exclusive_group(required=True)
    runtime.add_argument("--runtime-archive", type=Path)
    runtime.add_argument("--download-runtime", action="store_true")
    parser.add_argument("--commit", help="Full public commit; omitted builds are unpublished previews.")
    parser.add_argument("--previous-site", type=Path, help="Restore and validate previously archived version assets.")
    args = parser.parse_args()
    try:
        with tempfile.TemporaryDirectory(prefix="algo2lean-runtime-") as temporary:
            archive = args.runtime_archive
            if args.download_runtime:
                configuration = json.loads((ROOT / "browser-runtime.json").read_text(encoding="utf-8"))
                archive = Path(temporary) / "runtime.tar.bz2"
                with urlopen(configuration["url"], timeout=120) as response:
                    archive.write_bytes(response.read(40 * 1024 * 1024))
            version, files = release_files(ROOT, archive, args.commit)
            target = write_site(args.output, version, files, args.previous_site)
            print("Built " + str(target))
    except (OSError, ValueError, KeyError, tarfile.TarError) as error:
        parser.exit(1, str(error) + "\n")


if __name__ == "__main__":
    main()
