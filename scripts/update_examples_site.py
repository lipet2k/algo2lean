"""Publish current examples while retaining the exact archived compiler releases.

The current editor loads its compiler and runtime from the existing release. Static
catalog files supply example sources and proofs, without modifying compiler.zip,
the release manifest, the runtime, or any versioned website directory.
"""

import argparse
import io
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from scripts.build_site import digest, encoded, restore_versions, snapshot, verify_release
from scripts.release_site import api, download_asset, earlier_release, extract_site_archive, release_asset


def validate_compiler(root, release):
    """Permit catalog edits, but require the exact released compiler semantics."""
    config = json.loads((release / "release-config.json").read_text(encoding="utf-8"))
    archive = (release / "compiler.zip").read_bytes()
    if config.get("preview") or not re.fullmatch(r"[0-9a-f]{40}", config.get("commit") or ""):
        raise ValueError("Current examples require a published compiler release.")
    if digest(archive) != config["compiler_archive_sha256"]:
        raise ValueError("The archived compiler does not match its recorded hash.")
    with zipfile.ZipFile(io.BytesIO(archive)) as bundle:
        frozen = {name: bundle.read(name) for name in bundle.namelist()
                  if ((name.startswith("algo2lean/") and name.endswith(".py") and
                       name != "algo2lean/editor_examples.py") or
                      name.startswith("Algo2LeanLib/") or
                      name in {"Algo2Lean.lean", "lean-toolchain", "publication.json"})}
    local = {}
    for directory, suffix in (("algo2lean", ".py"), ("Algo2LeanLib", ".lean")):
        for path in sorted((root / directory).rglob("*" + suffix)):
            name = path.relative_to(root).as_posix()
            if name != "algo2lean/editor_examples.py":
                local[name] = path.read_bytes()
    for name in ("Algo2Lean.lean", "lean-toolchain", "publication.json"):
        local[name] = (root / name).read_bytes()
    if local != frozen:
        changed = sorted(name for name in local.keys() | frozen.keys()
                         if local.get(name) != frozen.get(name))
        raise ValueError("Compiler changes require a new release: " + ", ".join(changed))
    return config


def load_catalog(root):
    """Use the local catalog API so hosted and local example folders agree."""
    command = """
import json
from algo2lean.browser import request
catalog = request('/api/examples')
assert catalog['status'] == 200, catalog
projects = {}
for example in catalog['body']['examples']:
    identifier = example.get('project_id')
    if identifier is not None:
        project = request('/api/example-project/' + identifier)
        assert project['status'] == 200, project
        projects[identifier] = project['body']
print(json.dumps({'catalog': catalog['body'], 'projects': projects}))
"""
    return json.loads(subprocess.check_output([sys.executable, "-c", command], cwd=root, text=True))


def current_release(repository, version):
    """Do not let a delayed example update replace a newer compiler deployment."""
    release = api(repository, "/releases/tags/v" + version)
    if release.get("draft") or not release.get("published_at"):
        raise ValueError("Current examples require an already published release.")
    releases, page = [], 1
    while True:
        batch = api(repository, "/releases?per_page=100&page=" + str(page))
        releases.extend(batch)
        if len(batch) < 100:
            break
        page += 1
    earlier_release(releases, release)
    return release


def build_current_site(root, previous, output, commit):
    """Write a fresh site with immutable versions and a separately identified catalog."""
    if not re.fullmatch(r"[0-9a-f]{40}", commit or ""):
        raise ValueError("Use the full public commit identifying the current examples.")
    metadata = json.loads((root / "publication.json").read_text(encoding="utf-8"))
    version = metadata["version"]
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9.+-]*", version):
        raise ValueError("Invalid compiler version.")
    release = previous / "versions" / ("v" + version)
    verify_release(release)
    config = validate_compiler(root, release)
    versions = json.loads((previous / "versions.json").read_text(encoding="utf-8"))
    if versions.get("latest") != version or config.get("version") != version:
        raise ValueError("Current examples must use the latest archived compiler version.")
    if output.exists() and any(output.iterdir()):
        raise ValueError("Use an empty output directory for the current examples site.")
    catalog = load_catalog(root)
    files = {"examples/catalog.json": encoded(catalog["catalog"])}
    for identifier, project in catalog["projects"].items():
        if not re.fullmatch(r"[A-Za-z0-9_-]+", identifier):
            raise ValueError("Invalid example project identifier.")
        files["examples/projects/" + identifier + ".json"] = encoded(project)
    manifest = {
        "schema_version": 1, "catalog_commit": commit,
        "compiler": {key: config[key] for key in
                     ("version", "commit", "bundle_sha256", "compiler_archive_sha256")},
        "files": {name: digest(contents) for name, contents in sorted(files.items())},
    }
    files["example-manifest.json"] = encoded(manifest)
    for path in sorted((root / "editor").iterdir()):
        if path.suffix in {".html", ".js", ".css"} or path.name == "analysis_export.py":
            files[path.name] = path.read_bytes()
    files["release-config.json"] = encoded({**config, "compiler_base": "../versions/v" + version + "/"})
    page = files["index.html"].decode("utf-8")
    page = page.replace('href="/', 'href="').replace('src="/', 'src="')
    # The editor reads compiler_base from release-config.json to show the
    # current-examples links; only the static catalog script is injected here.
    page = page.replace('<script type="module" src="app.js">',
                        '<script src="browser-host.js" defer></script>\n'
                        '  <script src="current-examples.js" defer></script>\n'
                        '  <script type="module" src="app.js">')
    files["index.html"] = page.encode("utf-8")
    files["CITATION.cff"] = (release / "CITATION.cff").read_bytes()
    restore_versions(previous, output)
    for name in ("versions.json", "versions.html"):
        shutil.copyfile(previous / name, output / name)
    current = output / "current"
    for name, contents in files.items():
        path = current / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(contents)
    (output / "index.html").write_text(
        '<!doctype html><html lang="en"><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width, initial-scale=1">'
        '<meta http-equiv="refresh" content="0;url=current/">'
        '<title>Algo2Lean</title><a href="current/">Open Algo2Lean</a> · '
        '<a href="versions.html">Compiler versions</a></html>\n', encoding="utf-8")
    (output / ".nojekyll").write_text("", encoding="utf-8")
    if snapshot(previous / "versions") != snapshot(output / "versions"):
        raise ValueError("An archived compiler release changed while building the catalog.")
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "dist/site")
    parser.add_argument("--release-archive", type=Path, help="Existing algo2lean-site.zip; otherwise download the current release asset.")
    parser.add_argument("--commit", required=True, help="Full public commit for this example catalog.")
    args = parser.parse_args()
    try:
        with tempfile.TemporaryDirectory(prefix="algo2lean-current-examples-") as directory:
            temporary = Path(directory)
            archive = args.release_archive
            if archive is None:
                metadata = json.loads((ROOT / "publication.json").read_text(encoding="utf-8"))
                repository = metadata["repository_url"].removeprefix("https://github.com/")
                if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository):
                    raise ValueError("Configure a public GitHub repository in publication.json.")
                release = current_release(repository, metadata["version"])
                asset = release_asset(release)
                if asset is None:
                    raise ValueError("The current compiler release has no archived website.")
                archive = temporary / "algo2lean-site.zip"
                download_asset(asset, archive)
            previous = temporary / "previous"
            extract_site_archive(archive, previous)
            manifest = build_current_site(ROOT, previous, args.output.resolve(), args.commit)
            print("Built current examples at " + str(args.output.resolve() / "current") +
                  " using unchanged compiler v" + manifest["compiler"]["version"])
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError, zipfile.BadZipFile) as error:
        parser.exit(1, str(error) + "\n")


if __name__ == "__main__":
    main()
