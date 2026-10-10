"""Run the editor regression suites when optional Node.js is available."""

from pathlib import Path
import shutil
import subprocess
import unittest


class EditorTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("node"), "Node.js is optional; install it to test browser drafts")
    def test_browser_draft_regressions(self):
        root = Path(__file__).resolve().parents[1]
        result = subprocess.run(
            [shutil.which("node"), "--test", *map(str, sorted((root / "tests").glob("test_*.js")))],
            cwd=root,
            capture_output=True,
            text=True,
            timeout=30,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
