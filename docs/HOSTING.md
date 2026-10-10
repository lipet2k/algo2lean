# Browser compiler and version archive

Algo2Lean can build a static website that compiles `.algo` programs entirely in
the visitor's browser. The Python compiler runs in a Web Worker using a pinned
Pyodide runtime. The runtime, compiler, editor, and shared Lean libraries are
included in the site, so compilation does not send source to a server or load
compiler dependencies from a CDN.

Building the site creates files; it does not publish them or configure a domain.
The Python editor remains available through `python3 -m algo2lean serve --open`.

## Build and preview

Run from the repository root:

```sh
python3 scripts/build_site.py --output dist/site --download-runtime
python3 -m http.server 8000 --directory dist/site
```

Open `http://localhost:8000` in a browser. The builder downloads the official
Pyodide `314.0.7` runtime archive and checks its pinned SHA-256 digest before
using it. To build with an archive already downloaded, use:

```sh
python3 scripts/build_site.py --output dist/site \
  --runtime-archive /path/to/pyodide-core-314.0.7.tar.bz2
```

The same digest check applies to the supplied archive. Serve the output over
HTTP or HTTPS; opening its HTML directly as a `file:` URL does not provide the
browser facilities required by the worker.

The builder reads the version and citation from `publication.json`. It writes
the versioned compiler under `dist/site/versions/v<VERSION>/`, an entry page at
the root, and `versions.html` for the archive. Each version retains its matching
runtime, libraries, and editor assets.

## Identify and preserve releases

For a published build, supply the full commit SHA from the public repository:

```sh
python3 scripts/build_site.py --output dist/site --download-runtime \
  --commit FULL_PUBLIC_COMMIT_SHA
```

Omit `--commit` for an unpublished preview. Do not substitute a private
development revision for the public source identity. Before publishing, confirm
the version, citation, public repository URL, and release status in
`publication.json`, then regenerate `CITATION.cff`.

Keep the previous site's version directories when adding a release. Reusing the
same output directory preserves them; to recover an archive from another
location, use:

```sh
python3 scripts/build_site.py --output dist/site --download-runtime \
  --previous-site /path/to/previous/site
```

The builder validates the previous site's hashes. It refuses to replace an
existing version with different bytes. Fixes require a new version; do not
remove an archived release to reuse its name. Preserve a downloadable copy of
each built release as well as its source commit, so a hosting change need not
rebuild an old compiler with new dependencies.

Each version includes [third-party notices](../THIRD_PARTY_NOTICES.md) and the
runtime license texts. Preserve those files with the compiler and runtime.

Upload the contents of the completed `dist/site` directory to a static host such
as GitHub Pages. Publish the whole retained archive, including runtime assets;
uploading only the newest version loses older reproduction links. Domain and
HTTPS settings belong to the hosting provider and are separate from building
the website.

## Publish through GitHub Pages

The [Pages workflow](../.github/workflows/pages.yml) runs when a GitHub release
is published. In the repository's **Settings → Pages**, choose **GitHub Actions**
as the publishing source. The workflow does not configure a custom domain.

Before creating the release:

1. Set `publication.json` to `status: "release"`, choose a new version, and set
   `repository_url` to the public repository's exact HTTPS URL.
2. Run `python3 -m algo2lean.publication --write-citation`, check the changes, and
   commit them to the public repository.
3. Tag that commit `v<VERSION>`, matching the version in `publication.json`, and
   create the corresponding GitHub release.

Publishing triggers the compiler, editor, and Lean proof checks. The workflow
then checks out the release tag and verifies that it still identifies the commit
that triggered the workflow. It builds the site with that full public commit SHA,
attaches `algo2lean-site.zip` to the release, and deploys the same site to Pages.

The ZIP contains the complete website, including every earlier compiler version.
For subsequent releases, the workflow downloads this asset from the immediately
preceding published release and validates its archived files before adding the
new version. If the previous archive is missing or changed, publication fails
rather than silently dropping old versions. Keep these release assets: temporary
GitHub Actions artifacts are used only to transfer the deployment between jobs.

Rerunning a release reuses its existing ZIP only when its bytes are identical.
It never replaces an asset or moves a tag. A rerun for an older release also
refuses to replace the website after a newer release has been published.

### Repositories with immutable releases

GitHub prevents adding assets after an immutable release is published. In that
case, prepare and attach `algo2lean-site.zip` while the release is still a draft.
Build from the exact public tagged commit, with all previous versions restored:

```sh
python3 scripts/build_site.py --output dist/site --download-runtime \
  --commit FULL_PUBLIC_COMMIT_SHA --previous-site /path/to/previous/site
python3 -c 'from pathlib import Path; from scripts.release_site import archive_site; archive_site(Path("dist/site"), Path("dist/algo2lean-site.zip"))'
```

Omit `--previous-site` only for the first release. For later releases, obtain the
previous site by downloading and unpacking its `algo2lean-site.zip`. Upload the
new ZIP to the draft release before publishing it. The published-release workflow
rebuilds the site and requires an identical archive before deploying. If the
archive is absent or different, it stops; fix the release preparation process
and use a new version instead of replacing an immutable asset.

## Generation verification and Lean checking

Open the source or project and compile it with the selected compiler version.
Use **Verify generated files** to select the claimed `.lean` files. The verifier
reports missing, extra, or different files and compares exact generated content.
Folder selections preserve module paths: a file in the wrong module directory
does not match merely because its filename and contents match. Editing the source,
filename, or workspace clears the previous verification result and cancels any
comparison in progress.
The generation bundle and manifest download retain the sources, settings, and
artifact identities needed to reproduce that compilation.

A match means the supplied files agree exactly with this compiler's output for
those sources and settings. Imported sources must be present as well; a caller
file alone does not identify the contents of its dependencies.

The same comparison is available locally with the matching compiler version:

```sh
python3 -m algo2lean verify path/to/source.algo path/to/generated
python3 -m algo2lean verify path/to/source/main.algo path/to/generated \
  --project path/to/source
```

Select the unpacked generation bundle or a folder containing its generated Lean
files at their original relative paths. Add `--standalone` when comparing an
algorithm file with the shared library embedded. The command regenerates the
definitions, reports missing, extra, and changed Lean files, and checks any
supplied shared libraries. It leaves the files untouched and returns a nonzero
exit status when they differ. A supplied manifest is not accepted as proof of
matching output.

This comparison does not check a Lean proof and does not prove that the Python
compiler implements its intended semantics. Generated definitions and user-written
proofs have different roles: only the definitions are regenerated by the compiler.

The hosted editor has no local Lean process. Export the project or generated
files and check them with the pinned Lean toolchain locally. For a standalone
algorithm and its companion analysis, use:

```sh
python3 -m algo2lean analyze examples/factorial.algo examples/analysis/factorial.lean
```

For projects with imports, follow the [project guide](MODULES.md). The local
Python editor also provides **Check both files** and **Check analysis** when
Lean is installed.
