"""CI reuses proof checks while independently checking changed download packages."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from scripts.ci_plan import Plan, changed_paths, is_package_path, is_ui_path, main, plan_checks, required_mode


REPOSITORY = "example/algo2lean"
BASELINE = "a" * 40
HEAD = "b" * 40


def successful_run(sha=BASELINE, run_id=123, **changes):
    return {
        "id": run_id,
        "head_sha": sha,
        "event": "push",
        "head_branch": "main",
        "status": "completed",
        "conclusion": "success",
        "head_repository": {"full_name": REPOSITORY},
        "path": ".github/workflows/check.yml",
        **changes,
    }


def full_jobs(**changes):
    job = {
        "name": "Lean semantics and proofs",
        "conclusion": "success",
        "steps": [
            {"name": "Require Lean before running semantic checks", "conclusion": "success"},
            {"name": "Check compiler, generated definitions, and analysis proofs", "conclusion": "success"},
        ],
        **changes,
    }
    return {"total_count": 1, "jobs": [job]}


def package_jobs(**changes):
    job = {
        "name": "Lean download packages",
        "conclusion": "success",
        "steps": [
            {"name": "Require Lean before running semantic checks", "conclusion": "success"},
            {"name": "Check downloaded Lean projects", "conclusion": "success"},
        ],
        **changes,
    }
    return {"total_count": 1, "jobs": [job]}


class LeanPlanTests(unittest.TestCase):
    def plan(self, jobs=None, runs=None, paths=None, **options):
        responses = [{"workflow_runs": runs if runs is not None else [successful_run()]},
                     full_jobs() if jobs is None else jobs]
        with patch("scripts.ci_plan.github_api", side_effect=responses) as api, \
             patch("scripts.ci_plan.changed_paths", return_value=paths if paths is not None else ["editor/app.js"]):
            result = plan_checks("push", REPOSITORY, HEAD, **options)
        return result, api

    def test_main_emits_workflow_mode_and_verified_baselines(self):
        plans = [Plan("full", "Full verification required."),
                 Plan("packages", "Only package checks required.", BASELINE),
                 Plan("none", "Verified checks reused.", BASELINE, "c" * 40)]
        for selected in plans:
            with self.subTest(mode=selected.mode), tempfile.TemporaryDirectory() as directory:
                output = Path(directory) / "output"
                summary = Path(directory) / "summary"
                output.write_text("existing-output=true\n")
                summary.write_text("Existing summary\n")
                environment = {
                    "GITHUB_EVENT_NAME": "push", "GITHUB_REPOSITORY": REPOSITORY,
                    "GITHUB_RUN_ID": "456", "FORCE_FULL_LEAN": "false",
                    "GITHUB_OUTPUT": str(output), "GITHUB_STEP_SUMMARY": str(summary),
                }
                with patch.dict(os.environ, environment), \
                     patch("scripts.ci_plan.subprocess.check_output", return_value=HEAD + "\n") as git, \
                     patch("scripts.ci_plan.plan_checks", return_value=selected) as planner, \
                     patch("builtins.print"):
                    main()
                git.assert_called_once_with(["git", "rev-parse", "HEAD"], text=True)
                planner.assert_called_once_with("push", REPOSITORY, HEAD, force_full=False, current_run_id="456")
                self.assertEqual(output.read_text(), "existing-output=true\nlean-mode=" + selected.mode + "\n")
                report = summary.read_text()
                self.assertTrue(report.startswith("Existing summary\n## Lean check plan: " + selected.mode))
                self.assertIn(selected.reason, report)
                self.assertEqual("Verified full-check baseline:" in report, bool(selected.baseline))
                self.assertEqual("Verified package-check baseline:" in report, bool(selected.package_baseline))
                for baseline in [selected.baseline, selected.package_baseline]:
                    if baseline:
                        self.assertIn("`" + baseline + "`", report)

    def test_successful_full_check_allows_ui_changes(self):
        result, api = self.plan(paths=["editor/styles.css", "README.md", "tests/test_interface.js"])
        self.assertFalse(result.run_lean)
        self.assertEqual(result.mode, "none")
        self.assertEqual(result.baseline, BASELINE)
        self.assertEqual(api.call_count, 2)
        self.assertIn("workflows/check.yml/runs", api.call_args_list[0].args[0])
        self.assertIn("/123/jobs?filter=latest", api.call_args_list[1].args[0])

    def test_path_tiers_are_explicit_and_unknown_inputs_require_full_checks(self):
        for path in ["editor/styles.css", "docs/HOSTING.md", "docs/nested/GUIDE.md",
                     "tests/test_interface.js", "CHANGELOG.md"]:
            with self.subTest(path=path):
                self.assertTrue(is_ui_path(path))
                self.assertEqual(required_mode([path]), "none")
        for path in ["editor/analysis_export.py", "editor/server.py", "editor/compiler-worker.js",
                     "editor/browser-host.js", "scripts/build_site.py", "scripts/update_examples_site.py",
                     "scripts/release_site.py", "scripts/check_browser_runtime.mjs",
                     "tests/test_analysis_export.py", "tests/test_site_build.py",
                     "tests/test_current_examples_site.py", "tests/test_release_site.py"]:
            with self.subTest(path=path):
                self.assertFalse(is_ui_path(path))
                self.assertTrue(is_package_path(path))
                self.assertEqual(required_mode(["editor/styles.css", path]), "packages")
        for path in ["editor/new_adapter.py", "algo2lean/compiler.py", "algo2lean/Algo2Lean.lean",
                     "examples/analysis/Proof.lean", "scripts/ci_plan.py", "tests/test_ci_plan.py",
                     ".github/workflows/check.yml", "lean-toolchain", "docs/example.algo"]:
            with self.subTest(path=path):
                self.assertFalse(is_package_path(path))
                self.assertEqual(required_mode(["editor/styles.css", "editor/server.py", path]), "full")
        self.assertEqual(required_mode([]), "none")

    def test_packaging_edits_use_targeted_checks_from_verified_full_anchor(self):
        result, api = self.plan(paths=["editor/analysis_export.py", "docs/HOSTING.md"])
        self.assertEqual(result.mode, "packages")
        self.assertTrue(result.run_lean)
        self.assertEqual(result.baseline, BASELINE)
        self.assertEqual(api.call_count, 2)

    def test_successful_package_check_and_full_anchor_allow_later_ui_edits(self):
        package_sha = "c" * 40
        with patch("scripts.ci_plan.github_api", side_effect=[
            {"workflow_runs": [successful_run(package_sha, 124), successful_run(BASELINE, 123)]},
            package_jobs(), full_jobs(),
        ]), patch("scripts.ci_plan.changed_paths", side_effect=lambda base, head:
                  ["editor/styles.css"] if base == package_sha else
                  ["editor/analysis_export.py", "editor/styles.css"]):
            result = plan_checks("push", REPOSITORY, HEAD)
        self.assertEqual(result.mode, "none")
        self.assertEqual(result.baseline, BASELINE)

    def test_package_check_cannot_replace_full_proof_anchor(self):
        result, _ = self.plan(jobs=package_jobs(), paths=["editor/styles.css"])
        self.assertEqual(result.mode, "full")
        self.assertEqual(result.baseline, "")

    def test_new_packaging_edit_requires_another_package_check(self):
        package_sha = "c" * 40
        with patch("scripts.ci_plan.github_api", side_effect=[
            {"workflow_runs": [successful_run(package_sha, 124), successful_run(BASELINE, 123)]},
            package_jobs(), full_jobs(),
        ]), patch("scripts.ci_plan.changed_paths", return_value=["editor/analysis_export.py"]):
            result = plan_checks("push", REPOSITORY, HEAD)
        self.assertEqual(result.mode, "packages")
        self.assertEqual(result.baseline, BASELINE)

    def test_package_success_never_hides_unchecked_proof_change(self):
        package_sha = "c" * 40
        with patch("scripts.ci_plan.github_api", side_effect=[
            {"workflow_runs": [successful_run(package_sha, 124), successful_run(BASELINE, 123)]},
            package_jobs(),
        ]), patch("scripts.ci_plan.changed_paths", side_effect=lambda base, head:
                  ["editor/styles.css"] if base == package_sha else
                  ["editor/analysis_export.py", "examples/Proof.lean", "editor/styles.css"]):
            result = plan_checks("push", REPOSITORY, HEAD)
        self.assertEqual(result.mode, "full")

    def test_failed_skipped_or_incomplete_package_checks_do_not_allow_skipping(self):
        package_sha = "c" * 40
        cases = {
            "skipped job": package_jobs(conclusion="skipped"),
            "failed job": package_jobs(conclusion="failure"),
            "wrong job": package_jobs(name="Some unrelated package test"),
            "missing steps": package_jobs(steps=[]),
            "only installation": package_jobs(steps=package_jobs()["jobs"][0]["steps"][:1]),
            "skipped package step": package_jobs(steps=[
                package_jobs()["jobs"][0]["steps"][0],
                {"name": "Check downloaded Lean projects", "conclusion": "skipped"},
            ]),
            "duplicate jobs": {"total_count": 2, "jobs": package_jobs()["jobs"] * 2},
            "incomplete response": {"total_count": 101, "jobs": package_jobs()["jobs"]},
        }
        for description, jobs in cases.items():
            with self.subTest(description=description), \
                 patch("scripts.ci_plan.github_api", side_effect=[
                     {"workflow_runs": [successful_run(package_sha, 124), successful_run(BASELINE, 123)]},
                     jobs, full_jobs(),
                 ]), patch("scripts.ci_plan.changed_paths", side_effect=lambda base, head:
                           ["editor/styles.css"] if base == package_sha else
                           ["editor/server.py", "editor/styles.css"]):
                result = plan_checks("push", REPOSITORY, HEAD)
                self.assertEqual(result.mode, "packages")

    def test_ui_chain_can_look_back_past_skipped_runs_to_package_and_full_checks(self):
        package_sha, ui_sha = "c" * 40, "d" * 40
        with patch("scripts.ci_plan.github_api", side_effect=[
            {"workflow_runs": [successful_run(ui_sha, 125), successful_run(package_sha, 124),
                               successful_run(BASELINE, 123)]},
            {"total_count": 2, "jobs": [full_jobs(conclusion="skipped")["jobs"][0],
                                         package_jobs(conclusion="skipped")["jobs"][0]]},
            package_jobs(), full_jobs(),
        ]), patch("scripts.ci_plan.changed_paths", side_effect=lambda base, head:
                  ["editor/server.py", "editor/styles.css"] if base == BASELINE else
                  ["editor/styles.css"]):
            result = plan_checks("push", REPOSITORY, HEAD)
        self.assertEqual(result.mode, "none")
        self.assertEqual(result.baseline, BASELINE)

    def test_policy_and_workflow_changes_bootstrap_with_a_full_check(self):
        for path in ["scripts/ci_plan.py", "tests/test_ci_plan.py", ".github/workflows/check.yml"]:
            with self.subTest(path=path):
                result, api = self.plan(paths=["editor/server.py", path])
                self.assertEqual(result.mode, "full")
                self.assertEqual(api.call_count, 1)

    def test_pull_request_compares_the_actual_head_against_full_baseline(self):
        with patch("scripts.ci_plan.github_api", side_effect=[{"workflow_runs": [successful_run()]}, full_jobs()]), \
             patch("scripts.ci_plan.changed_paths", return_value=["editor/styles.css"]) as changes:
            result = plan_checks("pull_request", REPOSITORY, HEAD)
        self.assertFalse(result.run_lean)
        changes.assert_called_once_with(BASELINE, HEAD)

    def test_ui_update_chain_looks_back_past_a_skipped_lean_job(self):
        with patch("scripts.ci_plan.github_api", side_effect=[
            {"workflow_runs": [successful_run(HEAD, 124), successful_run(BASELINE, 123)]},
            full_jobs(conclusion="skipped"), full_jobs(),
        ]), patch("scripts.ci_plan.changed_paths", return_value=["editor/styles.css"]):
            result = plan_checks("push", REPOSITORY, "c" * 40)
        self.assertFalse(result.run_lean)
        self.assertEqual(result.baseline, BASELINE)

    def test_unrelated_missing_skipped_or_failed_jobs_cannot_establish_baseline(self):
        cases = {
            "unrelated job": full_jobs(name="Compiler and editor tests"),
            "missing job": {"total_count": 0, "jobs": []},
            "skipped job": full_jobs(conclusion="skipped"),
            "failed job": full_jobs(conclusion="failure"),
            "missing semantic steps": full_jobs(steps=[]),
            "only installation step": full_jobs(steps=full_jobs()["jobs"][0]["steps"][:1]),
            "skipped semantic step": full_jobs(steps=[
                full_jobs()["jobs"][0]["steps"][0],
                {"name": "Check compiler, generated definitions, and analysis proofs", "conclusion": "skipped"},
            ]),
            "failed installation step": full_jobs(steps=[
                {"name": "Require Lean before running semantic checks", "conclusion": "failure"},
                full_jobs()["jobs"][0]["steps"][1],
            ]),
            "duplicate Lean jobs": {"total_count": 2, "jobs": full_jobs()["jobs"] * 2},
        }
        for description, jobs in cases.items():
            with self.subTest(description=description):
                result, _ = self.plan(jobs=jobs)
                self.assertTrue(result.run_lean)
                self.assertEqual(result.baseline, "")

    def test_short_incomplete_jobs_response_requires_full_check(self):
        result, _ = self.plan(jobs={**full_jobs(), "total_count": 101})
        self.assertTrue(result.run_lean)

    def test_manual_release_reusable_and_forced_checks_do_not_query_api(self):
        for event, forced in [("workflow_dispatch", False), ("release", False),
                              ("workflow_call", False), ("", False),
                              ("push", True), ("pull_request", True)]:
            with self.subTest(event=event, forced=forced), \
                 patch("scripts.ci_plan.github_api") as api, \
                 patch("scripts.ci_plan.changed_paths") as changes:
                result = plan_checks(event, REPOSITORY, HEAD, force_full=forced)
                self.assertTrue(result.run_lean)
                api.assert_not_called()
                changes.assert_not_called()

    def test_allowlist_does_not_hide_proof_or_build_input_changes(self):
        for path in ["editor/worker.js", "editor/unknown.js",
                     "editor/nested/app.js", "tests/test_compiler.py", "tests/nested/test_ui.js",
                     "examples/Proof.lean", "examples/program.algo", "lean-toolchain",
                     "lakefile.lean", "lake-manifest.json", "pyproject.toml",
                     ".github/workflows/check.yml", "scripts/ci_plan.py", "docs/code.py",
                     "tests/test_ci_plan.py", "docs/Proof.lean"]:
            with self.subTest(path=path):
                self.assertFalse(is_ui_path(path))
                result, api = self.plan(paths=["editor/styles.css", path])
                self.assertEqual(result.mode, "full")
                self.assertEqual(api.call_count, 1)

    def test_untrusted_or_current_runs_are_not_reused(self):
        for changes in [{"event": "pull_request"}, {"head_branch": "feature"},
                        {"status": "in_progress"}, {"conclusion": "failure"},
                        {"head_repository": {"full_name": "other/algo2lean"}},
                        {"path": ".github/workflows/unrelated.yml"},
                        {"head_sha": "not-a-commit"}, {"id": "123"}, {"id": True}]:
            with self.subTest(changes=changes):
                result, api = self.plan(runs=[successful_run(**changes)])
                self.assertEqual(result.mode, "full")
                self.assertEqual(api.call_count, 1)
        result, api = self.plan(current_run_id="123")
        self.assertTrue(result.run_lean)
        self.assertEqual(api.call_count, 1)

    def test_invalid_repository_or_head_does_not_query_api(self):
        for repository, head in [("", HEAD), ("example/algo2lean/extra", HEAD),
                                 (REPOSITORY, "short"), (REPOSITORY, "g" * 40)]:
            with self.subTest(repository=repository, head=head), patch("scripts.ci_plan.github_api") as api:
                self.assertTrue(plan_checks("push", repository, head).run_lean)
                api.assert_not_called()

    def test_api_and_git_failures_fall_back_to_full_check(self):
        errors = [OSError("offline"), subprocess.CalledProcessError(1, ["gh", "api"]),
                  subprocess.TimeoutExpired(["gh", "api"], 20), ValueError("invalid JSON")]
        for error in errors:
            for stage in ["runs", "jobs", "git"]:
                with self.subTest(error=error, stage=stage), \
                     patch("scripts.ci_plan.github_api", side_effect=(
                         error if stage == "runs" else [{"workflow_runs": [successful_run()]}, error]
                     )), patch("scripts.ci_plan.changed_paths", side_effect=(
                         error if stage == "git" else None
                     ), return_value=["editor/styles.css"]):
                    result = plan_checks("push", REPOSITORY, HEAD)
                    self.assertTrue(result.run_lean)
                    self.assertEqual(result.baseline, "")

    def test_malformed_responses_fall_back_to_full_check(self):
        for response in [None, [], {}, {"workflow_runs": None}, {"workflow_runs": [None]}]:
            with self.subTest(response=response), patch("scripts.ci_plan.github_api", return_value=response):
                self.assertTrue(plan_checks("push", REPOSITORY, HEAD).run_lean)
        for response in [None, [], {}, {"jobs": []}, {"total_count": 1, "jobs": [None]},
                         {"total_count": 1, "jobs": "bad"}, full_jobs(steps=None)]:
            with self.subTest(jobs=response), \
                 patch("scripts.ci_plan.github_api", side_effect=[{"workflow_runs": [successful_run()]}, response]), \
                 patch("scripts.ci_plan.changed_paths", return_value=["editor/styles.css"]):
                self.assertTrue(plan_checks("push", REPOSITORY, HEAD).run_lean)


class LeanPlanGitHistoryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="algo2lean-ci-plan-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        previous_directory = Path.cwd()
        os.chdir(self.root)
        self.addCleanup(os.chdir, previous_directory)
        self.git("init", "-q")
        self.git("config", "user.name", "CI planner tests")
        self.git("config", "user.email", "ci-tests@example.invalid")
        self.base = self.commit({"editor/styles.css": "body { color: black; }\n",
                                 "examples/Proof.lean": "theorem sound : True := by trivial\n"})

    def git(self, *arguments):
        return subprocess.check_output(["git", *arguments], text=True, stderr=subprocess.PIPE).strip()

    def commit(self, files):
        for filename, contents in files.items():
            path = self.root / filename
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(contents, encoding="utf-8")
        self.git("add", "--all")
        self.git("commit", "-qm", "Test fixture change")
        return self.git("rev-parse", "HEAD")

    def test_ui_only_history_can_reuse_a_full_check(self):
        head = self.commit({"editor/styles.css": "body { color: blue; }\n"})
        self.assertEqual(changed_paths(self.base, head), ["editor/styles.css"])
        with patch("scripts.ci_plan.github_api", side_effect=[
            {"workflow_runs": [successful_run(self.base)]}, full_jobs()
        ]):
            result = plan_checks("push", REPOSITORY, head)
        self.assertFalse(result.run_lean)
        self.assertEqual(result.baseline, self.base)

    def test_ui_edit_after_unchecked_proof_change_requires_full_check(self):
        unchecked = self.commit({"examples/Proof.lean": "theorem sound : True := by sorry\n"})
        head = self.commit({"editor/styles.css": "body { color: blue; }\n"})
        self.assertEqual(changed_paths(unchecked, head), ["editor/styles.css"])
        self.assertIn("examples/Proof.lean", changed_paths(self.base, head))
        with patch("scripts.ci_plan.github_api", side_effect=[
            {"workflow_runs": [successful_run(unchecked, 124), successful_run(self.base, 123)]},
            full_jobs(conclusion="skipped"),
        ]) as api:
            result = plan_checks("push", REPOSITORY, head)
        self.assertTrue(result.run_lean)
        self.assertEqual(api.call_count, 2)

    def test_real_ui_package_ui_history_reuses_each_verified_layer(self):
        package = self.commit({"editor/analysis_export.py": "# Package implementation\n"})
        head = self.commit({"editor/styles.css": "body { color: blue; }\n"})
        self.assertEqual(changed_paths(package, head), ["editor/styles.css"])
        with patch("scripts.ci_plan.github_api", side_effect=[
            {"workflow_runs": [successful_run(package, 124), successful_run(self.base, 123)]},
            package_jobs(), full_jobs(),
        ]):
            result = plan_checks("push", REPOSITORY, head)
        self.assertEqual(result.mode, "none")
        self.assertEqual(result.baseline, self.base)

    def test_real_package_success_does_not_hide_an_unchecked_proof_commit(self):
        self.commit({"examples/Proof.lean": "theorem sound : True := by sorry\n"})
        package = self.commit({"editor/analysis_export.py": "# Package implementation\n"})
        head = self.commit({"editor/styles.css": "body { color: blue; }\n"})
        with patch("scripts.ci_plan.github_api", side_effect=[
            {"workflow_runs": [successful_run(package, 124), successful_run(self.base, 123)]},
            package_jobs(),
        ]):
            result = plan_checks("push", REPOSITORY, head)
        self.assertEqual(result.mode, "full")

    def test_rename_from_proof_file_to_ui_path_requires_full_check(self):
        self.git("mv", "examples/Proof.lean", "editor/app.js")
        head = self.commit({})
        self.assertEqual(set(changed_paths(self.base, head)), {"examples/Proof.lean", "editor/app.js"})
        with patch("scripts.ci_plan.github_api", return_value={"workflow_runs": [successful_run(self.base)]}) as api:
            self.assertTrue(plan_checks("push", REPOSITORY, head).run_lean)
        self.assertEqual(api.call_count, 1)

    def test_successful_check_on_a_nonancestor_cannot_be_reused(self):
        self.git("checkout", "-qb", "other")
        unrelated = self.commit({"editor/app.js": "// other branch\n"})
        self.git("checkout", "-q", "--detach", self.base)
        head = self.commit({"editor/styles.css": "body { color: blue; }\n"})
        self.assertIsNone(changed_paths(unrelated, head))
        with patch("scripts.ci_plan.github_api", return_value={"workflow_runs": [successful_run(unrelated)]}) as api:
            self.assertTrue(plan_checks("push", REPOSITORY, head).run_lean)
        self.assertEqual(api.call_count, 1)


if __name__ == "__main__":
    unittest.main()
