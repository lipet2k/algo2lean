"""Select no Lean work, exported-project builds, or the complete proof suite.

Every fast path requires a successful full check with unchanged proof inputs.
Package checks can then be reused independently of that full-check baseline.
GitHub API or history failures select the full suite. Compiler/editor tests and
the website's requirement for a successful check of current main are unchanged.
"""

from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import subprocess


UI_FILES = frozenset({
    "editor/app.js", "editor/styles.css", "editor/index.html",
    "editor/code-search.js", "editor/code-search.css", "editor/drafts.js",
    "editor/interface.js", "editor/proof-outline.js", "editor/publication.js",
    "README.md", "CHANGELOG.md",
})
PACKAGE_FILES = frozenset({
    "editor/analysis_export.py", "editor/server.py",
    "editor/compiler-worker.js", "editor/browser-host.js",
    "scripts/build_site.py", "scripts/update_examples_site.py",
    "scripts/release_site.py", "scripts/check_browser_runtime.mjs",
    "tests/test_analysis_export.py", "tests/test_site_build.py",
    "tests/test_current_examples_site.py", "tests/test_release_site.py",
})
SHA = re.compile(r"[0-9a-f]{40}\Z")


@dataclass(frozen=True)
class Plan:
    mode: str
    reason: str
    baseline: str = ""
    package_baseline: str = ""

    @property
    def run_lean(self):
        return self.mode != "none"


def is_ui_path(path):
    """Presentation and prose cannot change generated Lean or proof inputs."""
    return (path in UI_FILES or
            re.fullmatch(r"tests/test_[A-Za-z0-9_]+\.js", path) is not None or
            re.fullmatch(r"docs/(?:[A-Za-z0-9_-]+/)*[A-Za-z0-9_-]+\.md", path) is not None)


def is_package_path(path):
    return path in PACKAGE_FILES


def required_mode(paths):
    """Unknown inputs, including CI policy itself, require the complete suite."""
    if any(not is_ui_path(path) and not is_package_path(path) for path in paths):
        return "full"
    return "packages" if any(is_package_path(path) for path in paths) else "none"


def github_api(path):
    result = subprocess.run(["gh", "api", path], check=True, capture_output=True,
                            text=True, timeout=20)
    return json.loads(result.stdout)


def changed_paths(baseline, head):
    """Compare full history, including both sides of a rename; reject nonancestors."""
    ancestor = subprocess.run(["git", "merge-base", "--is-ancestor", baseline, head],
                              capture_output=True, timeout=20)
    if ancestor.returncode == 1:
        return None
    ancestor.check_returncode()
    diff = subprocess.run(["git", "diff", "--no-renames", "--name-only", "-z", baseline, head],
                          check=True, capture_output=True, timeout=20)
    return diff.stdout.decode("utf-8").rstrip("\0").split("\0") if diff.stdout else []


def passed_job(response, name, required_steps):
    """Only a completed job with all required checks establishes a baseline."""
    jobs = response["jobs"]
    if response["total_count"] != len(jobs):
        return False
    lean = [job for job in jobs if job.get("name") == name]
    if len(lean) != 1 or lean[0].get("conclusion") != "success":
        return False
    steps = lean[0].get("steps", [])
    return all(any(step.get("name") == name and step.get("conclusion") == "success"
                   for step in steps) for name in required_steps)


def full_lean_passed(response):
    return passed_job(response, "Lean semantics and proofs", (
        "Prepare pinned Mathlib for probability and real proofs",
        "Require Lean before running semantic checks",
        "Check compiler, generated definitions, and analysis proofs",
    ))


def packages_passed(response):
    return passed_job(response, "Lean download packages", (
        "Require Lean before running semantic checks",
        "Check downloaded Lean projects",
    ))


def plan_checks(event, repository, head, *, force_full=False, current_run_id=""):
    if force_full or event not in {"push", "pull_request"}:
        return Plan("full", "Manual and reusable/release checks run the full Lean suite.")
    if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository) or not SHA.fullmatch(head):
        return Plan("full", "Missing or invalid repository/commit identity.")
    try:
        # A bounded lookback limits API work. If no full check remains in this
        # window, run a new one rather than trusting a chain of skipped jobs.
        response = github_api(f"repos/{repository}/actions/workflows/check.yml/runs"
                              "?branch=main&event=push&status=success&per_page=100")
        package_baseline = ""
        for run in response["workflow_runs"]:
            if (run.get("event") != "push" or run.get("head_branch") != "main" or
                    run.get("status") != "completed" or run.get("conclusion") != "success" or
                    run.get("head_repository", {}).get("full_name") != repository or
                    run.get("path") != ".github/workflows/check.yml" or
                    str(run.get("id")) == str(current_run_id)):
                continue
            baseline = run.get("head_sha", "")
            run_id = run.get("id")
            if not isinstance(baseline, str) or not SHA.fullmatch(baseline) or type(run_id) is not int:
                continue
            paths = changed_paths(baseline, head)
            if paths is None or required_mode(paths) == "full":
                continue
            mode = required_mode(paths)
            jobs = github_api(f"repos/{repository}/actions/runs/{run_id}/jobs?filter=latest&per_page=100")
            if full_lean_passed(jobs):
                if mode == "none" or package_baseline:
                    return Plan("none", "Proof inputs and packages already passed Lean; only UI/documentation changed.",
                                baseline, package_baseline)
                return Plan("packages", "Proof inputs are unchanged; check downloaded projects and their imports only.",
                            baseline)
            if mode == "none" and not package_baseline and packages_passed(jobs):
                package_baseline = baseline
        return Plan("full", "No successful full Lean check with unchanged proof inputs was found.")
    except (OSError, ValueError, KeyError, TypeError, AttributeError, subprocess.SubprocessError):
        return Plan("full", "Baseline verification was unavailable; running the full Lean suite.")


def main():
    # HEAD is the commit actually checked out, including the synthetic merge for
    # a pull request, rather than an unchecked contributor branch tip.
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    plan = plan_checks(os.environ.get("GITHUB_EVENT_NAME", ""),
                       os.environ.get("GITHUB_REPOSITORY", ""), head,
                       force_full=os.environ.get("FORCE_FULL_LEAN") == "true",
                       current_run_id=os.environ.get("GITHUB_RUN_ID", ""))
    summary = (f"## Lean check plan: {plan.mode}\n\n" + plan.reason + "\n" +
               (f"\nVerified full-check baseline: `{plan.baseline}`.\n" if plan.baseline else "") +
               (f"\nVerified package-check baseline: `{plan.package_baseline}`.\n" if plan.package_baseline else ""))
    print(summary)
    if os.environ.get("GITHUB_OUTPUT"):
        with Path(os.environ["GITHUB_OUTPUT"]).open("a") as output:
            output.write(f"lean-mode={plan.mode}\n")
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with Path(os.environ["GITHUB_STEP_SUMMARY"]).open("a") as output:
            output.write(summary)


if __name__ == "__main__":
    main()
