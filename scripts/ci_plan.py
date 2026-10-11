"""Reuse a successful full Lean check only when cumulative changes are UI-only.

GitHub API or history failures deliberately select the full suite. This planner
does not skip compiler/editor tests or change the website's deployment gates.
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
SHA = re.compile(r"[0-9a-f]{40}\Z")


@dataclass(frozen=True)
class Plan:
    run_lean: bool
    reason: str
    baseline: str = ""


def is_ui_path(path):
    """Unknown files, compiler workers, proofs, and Python tests require Lean."""
    return path in UI_FILES or re.fullmatch(r"tests/test_[A-Za-z0-9_]+\.js", path) is not None


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


def full_lean_passed(response):
    """A skipped Lean job (another UI update) is not a full-check baseline."""
    jobs = response["jobs"]
    if response["total_count"] != len(jobs):
        return False
    lean = [job for job in jobs if job.get("name") == "Lean semantics and proofs"]
    if len(lean) != 1 or lean[0].get("conclusion") != "success":
        return False
    steps = lean[0].get("steps", [])
    return all(any(step.get("name") == name and step.get("conclusion") == "success"
                   for step in steps) for name in (
        "Require Lean before running semantic checks",
        "Check compiler, generated definitions, and analysis proofs",
    ))


def plan_checks(event, repository, head, *, force_full=False, current_run_id=""):
    if force_full or event not in {"push", "pull_request"}:
        return Plan(True, "Manual and reusable/release checks run the full Lean suite.")
    if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository) or not SHA.fullmatch(head):
        return Plan(True, "Missing or invalid repository/commit identity.")
    try:
        # A bounded lookback limits API work. If no full check remains in this
        # window, run a new one rather than trusting a chain of skipped jobs.
        response = github_api(f"repos/{repository}/actions/workflows/check.yml/runs"
                              "?branch=main&event=push&status=success&per_page=20")
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
            if paths is None or not all(is_ui_path(path) for path in paths):
                continue
            jobs = github_api(f"repos/{repository}/actions/runs/{run_id}/jobs?filter=latest&per_page=100")
            if full_lean_passed(jobs):
                return Plan(False, "Only UI/documentation changes since a successful full Lean check.", baseline)
        return Plan(True, "No successful full Lean check with unchanged proof inputs was found.")
    except (OSError, ValueError, KeyError, TypeError, AttributeError, subprocess.SubprocessError):
        return Plan(True, "Baseline verification was unavailable; running the full Lean suite.")


def main():
    # HEAD is the commit actually checked out, including the synthetic merge for
    # a pull request, rather than an unchecked contributor branch tip.
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    plan = plan_checks(os.environ.get("GITHUB_EVENT_NAME", ""),
                       os.environ.get("GITHUB_REPOSITORY", ""), head,
                       force_full=os.environ.get("FORCE_FULL_LEAN") == "true",
                       current_run_id=os.environ.get("GITHUB_RUN_ID", ""))
    summary = ("## Lean check plan\n\n" + plan.reason + "\n" +
               (f"\nVerified baseline: `{plan.baseline}`.\n" if plan.baseline else ""))
    print(summary)
    if os.environ.get("GITHUB_OUTPUT"):
        with Path(os.environ["GITHUB_OUTPUT"]).open("a") as output:
            output.write(f"run-lean={str(plan.run_lean).lower()}\n")
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with Path(os.environ["GITHUB_STEP_SUMMARY"]).open("a") as output:
            output.write(summary)


if __name__ == "__main__":
    main()
