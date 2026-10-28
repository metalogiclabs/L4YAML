"""Behavioral tests for the source-bound no-pop route diagnostic."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
TOOL = ROOT / "scripts" / "no_pop_contract_audit.py"


def fixture(*, carrier="SCompactSeqTail", paid=False, comment_only=False):
    route = "Or.inl ⟨[], by simp, fun _ _ => arbitrary⟩" if paid else "Or.inr trivial"
    first = (
        "-- exact (Classical.em (s_prep.indents = sc.indents)).elim "
        "(fun _ => Or.inr trivial) (fun _ => Or.inr trivial)\n"
        if comment_only else ""
    )
    branch = (
        "  exact Or.inr trivial\n" if comment_only else
        "  exact (Classical.em (s_prep.indents = sc.indents)).elim "
        f"(fun _ => {route}) (fun _ => Or.inr trivial)\n"
    )
    return (
        "lemma indicator_open_map\n"
        "    (h_res_land : (∃ ks, ∀ sp_end, SCompactMapTail k sp_land sp_end → P sp_end) ∨ True) := by\n"
        "  exact trivial\n"
        "lemma accum_block_on_pendingBlock\n"
        f"    (h_closeF_old : ∀ sp_end, {carrier} n sp_mid sp_end → ResumeFrames P ks sp_end) := by\n"
        + first + branch +
        "lemma accum_block_on_pendingBlockContent\n"
        f"    (h_closeF_old : ∀ sp_end, {carrier} n sp_mid sp_end → ResumeFrames P ks sp_end) := by\n"
        + branch
    )


def run_tool(source, extra_args=()):
    with tempfile.TemporaryDirectory() as folder:
        path = Path(folder) / "StreamAccum.lean"
        path.write_text(source, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, str(TOOL), "--source", str(path), "--sha", "test-sha", *extra_args],
            capture_output=True, text=True,
        )
        return proc


class NoPopContractAuditTests(unittest.TestCase):
    def test_reports_both_unpaid_same_level_routes_and_tail_type_gap(self):
        result = run_tool(fixture())
        self.assertEqual(result.returncode, 0, result.stderr)
        data = json.loads(result.stdout)
        self.assertEqual(data["source_sha"], "test-sha")
        self.assertEqual(data["target_tail"], "SCompactMapTail")
        self.assertEqual(len(data["builders"]), 2)
        self.assertEqual(
            {x["name"]: (x["carrier_tail"], x["same_level_declined"], x["type_gap_candidate"])
             for x in data["builders"]},
            {
                "accum_block_on_pendingBlock": ("SCompactSeqTail", True, True),
                "accum_block_on_pendingBlockContent": ("SCompactSeqTail", True, True),
            },
        )
        self.assertEqual(data["verification_boundary"], "STATIC_SOURCE_AUDIT_ONLY")

    def test_paid_branch_does_not_read_as_declined(self):
        result = run_tool(fixture(paid=True))
        self.assertEqual(result.returncode, 0, result.stderr)
        data = json.loads(result.stdout)
        self.assertTrue(all(not x["same_level_declined"] for x in data["builders"]))

    def test_matched_tail_types_do_not_report_type_gap(self):
        result = run_tool(fixture(carrier="SCompactMapTail"))
        self.assertEqual(result.returncode, 0, result.stderr)
        data = json.loads(result.stdout)
        self.assertTrue(all(not x["type_gap_candidate"] for x in data["builders"]))

    def test_comments_cannot_satisfy_branch_fingerprint(self):
        result = run_tool(fixture(comment_only=True))
        self.assertEqual(result.returncode, 0, result.stderr)
        data = json.loads(result.stdout)
        self.assertTrue(all(not x["same_level_declined"] for x in data["builders"]))

    def test_absent_essential_lemma_fails_closed(self):
        result = run_tool(fixture().replace("lemma indicator_open_map", "lemma renamed_opener"))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("indicator_open_map", result.stderr)

    def test_markdown_certificate_distinguishes_candidate_from_proof(self):
        result = run_tool(fixture(), ("--format", "markdown"))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("test-sha", result.stdout)
        self.assertIn("CANDIDATE", result.stdout)
        self.assertIn("STATIC_SOURCE_AUDIT_ONLY", result.stdout)
        self.assertIn("SCompactSeqTail", result.stdout)
        self.assertIn("SCompactMapTail", result.stdout)


if __name__ == "__main__":
    unittest.main()
