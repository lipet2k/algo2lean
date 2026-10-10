"""Release assets stay reproducible, complete, and immutable across versions."""

import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
import zipfile

from scripts.build_site import (RUNTIME_FILES, compiler_files, digest, encoded,
                                release_files, runtime_files, snapshot,
                                verify_release, write_site, zip_bytes)


class SiteBuildTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def minimal_release(self):
        for name, contents in {
            "algo2lean/__init__.py": "", "algo2lean/browser.py": "# bridge\n",
            "Algo2Lean.lean": "-- runtime\n", "Algo2LeanLib/Modules.lean": "-- modules\n",
            "lean-toolchain": "leanprover/lean4:v4.26.0\n", "LICENSE": "License\n",
            "publication.json": '{"version":"0.1.0"}', "CITATION.cff": "citation\n",
            "THIRD_PARTY_NOTICES.md": "notices\n", "licenses/runtime.txt": "runtime license\n",
            "examples/main.algo": "def f() -> Int:\n    return 1\n",
            "editor/index.html": '<script src="/app.js" defer></script>',
            "editor/app.js": "// editor\n", "editor/browser-host.js": "// bridge\n",
            "editor/compiler-worker.js": "// worker\n",
            "AGENTS.md": "internal instructions", "private.txt": "private",
            "algo2lean/__pycache__/module.pyc": "cache",
        }.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(contents, encoding="utf-8")
        archive = self.root / "runtime.tar.bz2"
        with tarfile.open(archive, "w:bz2") as tar:
            for name in RUNTIME_FILES:
                contents = name.encode()
                info = tarfile.TarInfo("pyodide/" + name)
                info.size = len(contents)
                tar.addfile(info, io.BytesIO(contents))
        configuration = {"version": "314.0.7", "sha256": digest(archive.read_bytes())}
        (self.root / "browser-runtime.json").write_bytes(encoded(configuration))
        return archive

    def test_bundle_is_deterministic_and_excludes_internal_files(self):
        archive = self.minimal_release()
        version, first = release_files(self.root, archive)
        _, second = release_files(self.root, archive)
        self.assertEqual(first, second)
        self.assertEqual(version, "0.1.0")
        with zipfile.ZipFile(io.BytesIO(first["compiler.zip"])) as bundle:
            names = set(bundle.namelist())
            self.assertIn("Algo2Lean.lean", names)
            self.assertIn("Algo2LeanLib/Modules.lean", names)
            self.assertIn("publication.json", names)
            self.assertIn("release-manifest.json", names)
            self.assertNotIn("AGENTS.md", names)
            self.assertFalse(any("private" in name or "__pycache__" in name for name in names))
        page = first["index.html"].decode()
        self.assertLess(page.index('src="browser-host.js"'), page.index('src="app.js"'))
        self.assertNotIn('src="/', page)
        config = json.loads(first["release-config.json"])
        self.assertEqual(config["compiler_archive_sha256"], digest(first["compiler.zip"]))
        self.assertTrue(config["preview"])
        self.assertIsNone(config["commit"])

    def test_runtime_checksum_is_required(self):
        archive = self.minimal_release()
        with self.assertRaisesRegex(ValueError, "checksum"):
            runtime_files(archive, {"sha256": "0" * 64})

    def test_new_release_preserves_previous_bytes_and_rejects_replacement(self):
        archive = self.minimal_release()
        version, first = release_files(self.root, archive, "a" * 40)
        output = self.root / "site"
        target = write_site(output, version, first)
        before = snapshot(target)
        write_site(output, version, first)
        (self.root / "publication.json").write_text('{"version":"0.1.1"}')
        version2, second = release_files(self.root, archive, "b" * 40)
        write_site(output, version2, second)
        self.assertEqual(snapshot(target), before)
        self.assertEqual(len(json.loads((output / "versions.json").read_text())["versions"]), 2)
        with self.assertRaisesRegex(ValueError, "Refusing"):
            write_site(output, version, {**first, "app.js": b"changed"})
        verify_release(target)
        (target / "app.js").write_text("changed")
        with self.assertRaisesRegex(ValueError, "changed"):
            verify_release(target)

    def test_restore_validates_previous_assets(self):
        archive = self.minimal_release()
        version, files = release_files(self.root, archive)
        previous = self.root / "previous"
        write_site(previous, version, files)
        fresh = self.root / "fresh"
        write_site(fresh, version, files, previous)
        self.assertEqual(snapshot(previous), snapshot(fresh))
        (previous / "versions" / ("v" + version) / "unexpected.txt").write_text("extra")
        with self.assertRaisesRegex(ValueError, "changed"):
            write_site(self.root / "broken", version, files, previous)

    def test_archive_order_and_timestamps_do_not_depend_on_environment(self):
        self.assertEqual(zip_bytes({"b": b"2", "a": b"1"}), zip_bytes({"a": b"1", "b": b"2"}))

    def test_public_commit_must_be_full_sha(self):
        archive = self.minimal_release()
        with self.assertRaisesRegex(ValueError, "complete public Git"):
            release_files(self.root, archive, "main")


if __name__ == "__main__":
    unittest.main()
