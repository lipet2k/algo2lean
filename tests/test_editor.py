"""Run the editor regression suite when the optional Node.js toolchain is installed."""

from pathlib import Path
import shutil
import subprocess
import unittest


class EditorTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("npm"), "Node.js is optional; install it with npm to test the editor")
    def test_editor_regressions(self):
        root = Path(__file__).resolve().parents[1]
        if not (root / "node_modules" / ".bin" / "vitest").exists():
            self.skipTest("Run npm ci to install the editor test runner")
        result = subprocess.run(
            [shutil.which("npm"), "test", "--silent"],
            cwd=root,
            capture_output=True,
            text=True,
            timeout=600,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
