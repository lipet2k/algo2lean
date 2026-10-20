"""Current example updates use a frozen compiler and preserve release archives."""

import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch

from scripts.build_site import RUNTIME_FILES, digest, encoded, release_files, snapshot, write_site
from scripts.update_examples_site import build_current_site, current_release


class CurrentExamplesSiteTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for name, contents in {
            "algo2lean/__init__.py": "", "algo2lean/browser.py": "# compiler API\n",
            "algo2lean/editor_examples.py": "# catalog\n",
            "Algo2Lean.lean": "-- runtime\n", "Algo2LeanLib/Modules.lean": "-- modules\n",
            "lean-toolchain": "leanprover/lean4:v4.33.1\n", "LICENSE": "License\n",
            "publication.json": '{"version":"0.1.4"}', "CITATION.cff": "citation\n",
            "THIRD_PARTY_NOTICES.md": "notices\n", "licenses/runtime.txt": "runtime license\n",
            "examples/main.algo": "def f() -> Int:\n    return 1\n",
            "editor/index.html": '<script type="module" src="app.js"></script>',
            "editor/app.js": "// editor\n", "editor/browser-host.js": "// frozen bridge\n",
            "editor/compiler-worker.js": "// frozen worker\n",
            "editor/current-examples.js": "// static example catalog\n",
            "editor/analysis_export.py": "# editor-only analysis packaging\n",
        }.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(contents, encoding="utf-8")
        runtime = self.root / "runtime.tar.bz2"
        with tarfile.open(runtime, "w:bz2") as bundle:
            for name in RUNTIME_FILES:
                contents = name.encode()
                item = tarfile.TarInfo("pyodide/" + name)
                item.size = len(contents)
                bundle.addfile(item, io.BytesIO(contents))
        (self.root / "browser-runtime.json").write_bytes(encoded({
            "version": "314.0.7", "sha256": digest(runtime.read_bytes()),
        }))
        version, files = release_files(self.root, runtime, "a" * 40)
        self.previous = self.root / "previous"
        write_site(self.previous, version, files)
        self.output = self.root / "new-site"
        self.catalog = {
            "catalog": {"examples": [{"project_id": "prim", "name": "Prim", "source": "prim code"}]},
            "projects": {"prim": {"name": "Prim", "entry": "prim/prim_fibonacci.algo",
                                  "sources": {"prim/prim_fibonacci.algo": "prim code"},
                                  "analyses": {"Algo.prim.prim_fibonacci.Analysis": "proof"}}},
        }
        mock = patch("scripts.update_examples_site.load_catalog", return_value=self.catalog)
        mock.start()
        self.addCleanup(mock.stop)

    def build(self, commit="b" * 40):
        return build_current_site(self.root, self.previous, self.output, commit)

    def test_new_catalog_keeps_every_archived_byte_and_compiler_identity(self):
        before = snapshot(self.previous / "versions")
        (self.root / "algo2lean/editor_examples.py").write_text("# newer catalog\n")
        (self.root / "examples/prim.algo").write_text("new example\n")
        manifest = self.build()
        self.assertEqual(snapshot(self.output / "versions"), before)
        self.assertEqual(manifest["catalog_commit"], "b" * 40)
        self.assertEqual(manifest["compiler"]["commit"], "a" * 40)
        self.assertEqual(manifest["compiler"]["version"], "0.1.4")
        current = self.output / "current"
        self.assertEqual(json.loads((current / "examples/catalog.json").read_text()), self.catalog["catalog"])
        self.assertEqual(json.loads((current / "examples/projects/prim.json").read_text()), self.catalog["projects"]["prim"])
        for name, checksum in manifest["files"].items():
            self.assertEqual(digest((current / name).read_bytes()), checksum)
        self.assertFalse((current / "compiler.zip").exists())
        self.assertEqual((current / "compiler-worker.js").read_bytes(), (self.root / "editor/compiler-worker.js").read_bytes())
        self.assertEqual((current / "browser-host.js").read_bytes(), (self.root / "editor/browser-host.js").read_bytes())
        self.assertEqual((current / "analysis_export.py").read_bytes(), (self.root / "editor/analysis_export.py").read_bytes())
        config = json.loads((current / "release-config.json").read_text())
        self.assertEqual(config["compiler_base"], "../versions/v0.1.4/")
        frozen = json.loads((self.previous / "versions/v0.1.4/release-config.json").read_text())
        self.assertEqual({k: v for k, v in config.items() if k != "compiler_base"}, frozen)
        page = (current / "index.html").read_text()
        self.assertLess(page.index('src="browser-host.js"'), page.index('src="current-examples.js"'))
        self.assertLess(page.index('src="current-examples.js"'), page.index('src="app.js"'))
        self.assertNotIn('src="/', page)
        self.assertIn('url=current/', (self.output / "index.html").read_text())

    def test_changed_compiler_or_shared_library_requires_new_release(self):
        for name in ("algo2lean/browser.py", "Algo2LeanLib/Modules.lean", "Algo2Lean.lean", "lean-toolchain"):
            path = self.root / name
            original = path.read_bytes()
            path.write_bytes(original + b"changed\n")
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, "Compiler changes require a new release"):
                self.build()
            path.write_bytes(original)
        self.assertFalse(self.output.exists())

    def test_missing_or_new_compiler_module_is_not_silently_allowed(self):
        path = self.root / "algo2lean/new_semantics.py"
        path.write_text("new compiler code\n")
        with self.assertRaisesRegex(ValueError, "new_semantics"):
            self.build()

    def test_invalid_commit_and_project_paths_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "full public commit"):
            self.build("main")
        self.catalog["projects"]["../escape"] = {}
        with self.assertRaisesRegex(ValueError, "Invalid example project"):
            self.build()
        self.assertFalse(self.output.exists())

    def test_changed_archive_fails_before_building_any_current_files(self):
        (self.previous / "versions/v0.1.4/app.js").write_text("changed archived editor\n")
        with self.assertRaisesRegex(ValueError, "Archived release assets have changed"):
            self.build()
        self.assertFalse(self.output.exists())

    def test_nonempty_output_is_not_overwritten(self):
        self.output.mkdir()
        (self.output / "keep.txt").write_text("existing file")
        with self.assertRaisesRegex(ValueError, "empty output"):
            self.build()
        self.assertEqual((self.output / "keep.txt").read_text(), "existing file")

    def test_delayed_catalog_update_cannot_replace_newer_release(self):
        release = {"id": 1, "tag_name": "v0.1.4", "published_at": "2026-10-10T10:00:00Z"}
        newer = {"id": 2, "tag_name": "v0.1.5", "published_at": "2026-10-11T10:00:00Z"}
        with patch("scripts.update_examples_site.api", side_effect=[release, [release, newer]]):
            with self.assertRaisesRegex(ValueError, "newer release"):
                current_release("example/algo2lean", "0.1.4")
        with patch("scripts.update_examples_site.api", return_value={**release, "draft": True}):
            with self.assertRaisesRegex(ValueError, "already published"):
                current_release("example/algo2lean", "0.1.4")


if __name__ == "__main__":
    unittest.main()
