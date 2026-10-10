"""Release publication preserves immutable output and every archived version."""

import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import zipfile

from scripts.release_site import (ASSET, archive_site, earlier_release, extract_site_archive,
                                  file_hash, prepare, release_asset, validate_release)


RELEASE = {"id": 2, "tag_name": "v0.1.0", "draft": False,
           "published_at": "2026-10-09T12:00:00Z", "assets": []}
EVENT = {"action": "published", "release": RELEASE,
         "repository": {"private": False, "html_url": "https://github.com/example/algo2lean"}}
METADATA = {"status": "release", "version": "0.1.0", "repository_url": "https://github.com/example/algo2lean"}


class ReleaseIdentityTests(unittest.TestCase):
    def test_tag_repository_status_and_commit_must_match(self):
        self.assertEqual(validate_release(EVENT, METADATA, "a" * 40, "a" * 40), RELEASE)
        cases = [(EVENT, {**METADATA, "status": "development"}, "a" * 40),
                 (EVENT, {**METADATA, "version": "0.2.0"}, "a" * 40),
                 (EVENT, {**METADATA, "repository_url": None}, "a" * 40),
                 (EVENT, METADATA, "b" * 40),
                 ({**EVENT, "action": "edited"}, METADATA, "a" * 40),
                 ({**EVENT, "repository": {**EVENT["repository"], "private": True}}, METADATA, "a" * 40)]
        for event, metadata, commit in cases:
            with self.subTest(event=event, metadata=metadata, commit=commit), self.assertRaises(ValueError):
                validate_release(event, metadata, commit, "a" * 40)

    def test_previous_release_includes_prereleases_but_ignores_drafts(self):
        previous = {**RELEASE, "id": 1, "published_at": "2026-10-08T12:00:00Z", "prerelease": True}
        draft = {**RELEASE, "id": 3, "published_at": None, "draft": True}
        self.assertEqual(earlier_release([RELEASE, previous, draft], RELEASE), previous)
        self.assertIsNone(earlier_release([RELEASE, draft], RELEASE))

    def test_older_release_cannot_replace_newer_pages(self):
        newer = {**RELEASE, "id": 3, "published_at": "2026-10-10T12:00:00Z"}
        with self.assertRaisesRegex(ValueError, "newer release"):
            earlier_release([RELEASE, newer], RELEASE)

    def test_archive_selection_requires_unique_exact_name(self):
        asset = {"name": ASSET}
        self.assertIsNone(release_asset(RELEASE))
        self.assertEqual(release_asset({**RELEASE, "assets": [asset]}), asset)
        with self.assertRaisesRegex(ValueError, "duplicate"):
            release_asset({**RELEASE, "assets": [asset, asset]})


class ReleaseArchiveTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="algo2lean-release-site-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def test_archive_round_trip_is_deterministic(self):
        site = self.root / "site"
        (site / "versions/v0.1.0/runtime").mkdir(parents=True)
        (site / "index.html").write_text("hello", encoding="utf-8")
        (site / "versions/v0.1.0/runtime/python.zip").write_bytes(bytes(range(256)))
        first, second = self.root / "first.zip", self.root / "second.zip"
        archive_site(site, first)
        archive_site(site, second)
        self.assertEqual(file_hash(first), file_hash(second))
        restored = self.root / "restored"
        extract_site_archive(first, restored)
        self.assertEqual((restored / "index.html").read_text(), "hello")
        self.assertEqual((restored / "versions/v0.1.0/runtime/python.zip").read_bytes(), bytes(range(256)))

    def test_archive_rejects_path_escape_and_links(self):
        for index, filename in enumerate(("../outside", "/absolute", "versions\\escape")):
            archive = self.root / (str(index) + ".zip")
            with zipfile.ZipFile(archive, "w") as output:
                output.writestr(filename, "x")
            with self.subTest(filename=filename), self.assertRaisesRegex(ValueError, "unsafe"):
                extract_site_archive(archive, self.root / ("extract" + str(index)))
        archive = self.root / "link.zip"
        with zipfile.ZipFile(archive, "w") as output:
            item = zipfile.ZipInfo("versions/link")
            item.external_attr = 0o120777 << 16
            output.writestr(item, "../../outside")
        with self.assertRaisesRegex(ValueError, "unsafe"):
            extract_site_archive(archive, self.root / "links")

    def test_archive_must_contain_versions(self):
        archive = self.root / "empty.zip"
        with zipfile.ZipFile(archive, "w") as output:
            output.writestr("index.html", "not an archived compiler site")
        with self.assertRaisesRegex(ValueError, "archived compiler versions"):
            extract_site_archive(archive, self.root / "extract")


class ReleaseUploadTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="algo2lean-upload-test-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.site = self.root / "site"
        self.output = self.root / ASSET
        self.event = self.root / "event.json"
        self.event.write_text(json.dumps({**EVENT, "repository": {**EVENT["repository"], "full_name": "example/algo2lean"}}))
        (self.root / "publication.json").write_text(json.dumps(METADATA))
        for mock in (patch("scripts.release_site.ROOT", self.root),
                     patch.dict(os.environ, {"GITHUB_EVENT_PATH": str(self.event), "GITHUB_SHA": "a" * 40}),
                     patch("scripts.release_site.subprocess.check_output", return_value="a" * 40)):
            mock.start()
            self.addCleanup(mock.stop)

    def fake_build(self, command, **kwargs):
        if "build_site.py" in command[1]:
            (self.site / "versions/v0.1.0").mkdir(parents=True)
            (self.site / "versions/v0.1.0/index.html").write_text("release")

    def test_missing_previous_archive_stops_before_build_or_upload(self):
        previous = {**RELEASE, "id": 1, "published_at": "2026-10-08T12:00:00Z", "tag_name": "v0.0.1"}
        with patch("scripts.release_site.api", side_effect=[RELEASE, [RELEASE, previous]]), \
             patch("scripts.release_site.subprocess.run") as run:
            with self.assertRaisesRegex(ValueError, "missing.*refusing"):
                prepare(self.site, self.output)
            run.assert_not_called()

    def test_immutable_release_requires_a_preattached_archive(self):
        with patch("scripts.release_site.api", return_value={**RELEASE, "immutable": True}), \
             patch("scripts.release_site.subprocess.run") as run:
            with self.assertRaisesRegex(ValueError, "immutable.*no site archive"):
                prepare(self.site, self.output)
            run.assert_not_called()

    def test_existing_identical_archive_is_reused_without_upload(self):
        current = {**RELEASE, "assets": [{"name": ASSET}]}
        def download(asset, target):
            target.write_bytes(self.output.read_bytes())
        with patch("scripts.release_site.api", side_effect=[current, [current]]), \
             patch("scripts.release_site.download_asset", side_effect=download), \
             patch("scripts.release_site.subprocess.run", side_effect=self.fake_build) as run:
            prepare(self.site, self.output)
            self.assertEqual(run.call_count, 1)

    def test_existing_different_archive_is_never_replaced(self):
        current = {**RELEASE, "assets": [{"name": ASSET}]}
        with patch("scripts.release_site.api", side_effect=[current, [current]]), \
             patch("scripts.release_site.download_asset", side_effect=lambda asset, target: target.write_bytes(b"different")), \
             patch("scripts.release_site.subprocess.run", side_effect=self.fake_build) as run:
            with self.assertRaisesRegex(ValueError, "never overwritten"):
                prepare(self.site, self.output)
            self.assertEqual(run.call_count, 1)

    def test_new_archive_upload_omits_clobber(self):
        with patch("scripts.release_site.api", side_effect=[RELEASE, [RELEASE]]), \
             patch("scripts.release_site.subprocess.run", side_effect=self.fake_build) as run:
            prepare(self.site, self.output)
            self.assertEqual(run.call_count, 2)
            self.assertEqual(run.call_args.args[0], ["gh", "release", "upload", "v0.1.0", str(self.output), "--repo", "example/algo2lean"])


if __name__ == "__main__":
    unittest.main()
