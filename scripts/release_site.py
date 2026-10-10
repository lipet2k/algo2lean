"""Build a Pages release while preserving the archives attached to earlier releases."""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import stat
import subprocess
import sys
import tempfile
from urllib.request import Request, urlopen
import zipfile

ROOT = Path(__file__).resolve().parents[1]
ASSET = "algo2lean-site.zip"


def api(repository, resource):
    request = Request("https://api.github.com/repos/" + repository + resource,
                      headers={"Accept": "application/vnd.github+json",
                               "Authorization": "Bearer " + os.environ["GH_TOKEN"],
                               "X-GitHub-Api-Version": "2022-11-28"})
    with urlopen(request, timeout=60) as response:
        return json.load(response)


def validate_release(event, metadata, commit, event_commit):
    release = event["release"]
    if event.get("action") != "published" or release.get("draft") or not release.get("published_at"):
        raise ValueError("Only a published release can deploy Pages.")
    if event["repository"].get("private"):
        raise ValueError("The public compiler must be released from a public repository.")
    if metadata["status"] != "release" or release["tag_name"] != "v" + metadata["version"]:
        raise ValueError("Set publication.json to release status and tag exactly v<version>.")
    if metadata.get("repository_url") != event["repository"]["html_url"]:
        raise ValueError("publication.json must name this public GitHub repository.")
    if commit != event_commit:
        raise ValueError("The release tag no longer matches the commit that triggered this workflow.")
    return release


def earlier_release(releases, current):
    key = lambda release: (release["published_at"], release["id"])
    published = [release for release in releases if not release.get("draft") and release.get("published_at")]
    if any(key(release) > key(current) for release in published):
        raise ValueError("A newer release is published. Refusing to replace its Pages deployment with an older version.")
    earlier = [release for release in published if key(release) < key(current)]
    return max(earlier, key=key) if earlier else None


def release_asset(release):
    assets = [asset for asset in release.get("assets", []) if asset["name"] == ASSET]
    if len(assets) > 1:
        raise ValueError("Release has duplicate site archives: " + release["tag_name"])
    return assets[0] if assets else None


def download_asset(asset, path):
    # Public download URLs need no token; authentication never follows redirects.
    address = asset["browser_download_url"]
    if not address.startswith("https://github.com/"):
        raise ValueError("The archive must be a public GitHub release asset.")
    with urlopen(address, timeout=120) as response, path.open("wb") as output:
        shutil.copyfileobj(response, output)
    digest = asset.get("digest")
    if digest and digest.startswith("sha256:") and file_hash(path) != digest[7:]:
        raise ValueError("The downloaded release archive does not match GitHub's asset digest.")


def file_hash(path):
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def extract_site_archive(path, destination):
    with zipfile.ZipFile(path) as archive:
        seen = set()
        for member in archive.infolist():
            relative = PurePosixPath(member.filename)
            mode = member.external_attr >> 16
            if (relative.is_absolute() or ".." in relative.parts or "\\" in member.filename or
                    member.filename in seen or stat.S_ISLNK(mode)):
                raise ValueError("The previous site archive contains an unsafe or duplicate path.")
            seen.add(member.filename)
            target = destination.joinpath(*relative.parts)
            if member.is_dir():
                target.mkdir(parents=True, exist_ok=True)
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                with archive.open(member) as source, target.open("xb") as output:
                    shutil.copyfileobj(source, output)
    if not (destination / "versions").is_dir():
        raise ValueError("The previous release archive does not contain archived compiler versions.")


def archive_site(site, output):
    output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(output, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for path in sorted(site.rglob("*")):
            if path.is_symlink():
                raise ValueError("The site must not contain symbolic links.")
            if path.is_file():
                item = zipfile.ZipInfo(path.relative_to(site).as_posix(), (2020, 1, 1, 0, 0, 0))
                item.compress_type = zipfile.ZIP_DEFLATED
                item.create_system = 3
                item.external_attr = 0o100644 << 16
                with path.open("rb") as source, archive.open(item, "w") as target:
                    shutil.copyfileobj(source, target)


def prepare(site, output):
    event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text(encoding="utf-8"))
    metadata = json.loads((ROOT / "publication.json").read_text(encoding="utf-8"))
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    current = validate_release(event, metadata, commit, os.environ["GITHUB_SHA"])
    repository = event["repository"]["full_name"]
    current = api(repository, "/releases/" + str(current["id"]))
    validate_release({**event, "release": current}, metadata, commit, os.environ["GITHUB_SHA"])
    existing = release_asset(current)
    if current.get("immutable") and existing is None:
        raise ValueError("This release is immutable and has no site archive. Attach algo2lean-site.zip to the draft before publishing an immutable release.")
    releases = []
    page = 1
    while True:
        batch = api(repository, "/releases?per_page=100&page=" + str(page))
        releases.extend(batch)
        if len(batch) < 100:
            break
        page += 1
    previous = earlier_release(releases, current)
    with tempfile.TemporaryDirectory(prefix="algo2lean-previous-site-") as directory:
        temporary = Path(directory)
        command = [sys.executable, str(ROOT / "scripts/build_site.py"), "--download-runtime",
                   "--output", str(site), "--commit", commit]
        if previous is not None:
            asset = release_asset(previous)
            if asset is None:
                raise ValueError("The previous release " + previous["tag_name"] + " is missing " + ASSET + "; refusing to discard its history.")
            downloaded = temporary / ASSET
            download_asset(asset, downloaded)
            restored = temporary / "site"
            extract_site_archive(downloaded, restored)
            command += ["--previous-site", str(restored)]
        subprocess.run(command, cwd=ROOT, check=True)
        archive_site(site, output)
        if existing is not None:
            downloaded = temporary / ("existing-" + ASSET)
            download_asset(existing, downloaded)
            if file_hash(output) != file_hash(downloaded):
                raise ValueError("The release already has a different site archive. Existing assets are never overwritten; publish a new version.")
            print("Reusing the identical archived site for " + current["tag_name"])
        else:
            # No --clobber: GitHub also rejects a competing upload of this name.
            subprocess.run(["gh", "release", "upload", current["tag_name"], str(output),
                            "--repo", repository], cwd=ROOT, check=True)
            print("Archived the complete site as " + ASSET)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--site", type=Path, default=ROOT / "dist/site")
    parser.add_argument("--archive", type=Path, default=ROOT / "dist" / ASSET)
    args = parser.parse_args()
    try:
        prepare(args.site.resolve(), args.archive.resolve())
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError, zipfile.BadZipFile) as error:
        parser.exit(1, str(error) + "\n")


if __name__ == "__main__":
    main()
