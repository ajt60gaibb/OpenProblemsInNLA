"""Read-only hash, source-import and existing local-record checks; never runs Lean."""
from pathlib import Path
import gzip
import hashlib
import json
import re

BASE = Path(__file__).resolve().parents[2]
REVIEW = Path(__file__).parent
SEALED = BASE / "development/PF03-agent-packaging-v1/project"
PUBLISH = BASE / "publication/PF03/nonnegative-and-positive-factorizations/PF-03/lean"
EVIDENCE = PUBLISH / "verification/local-2026-09-19"


def shab(b):
    return hashlib.sha256(b).hexdigest()


def sha(p):
    return shab(p.read_bytes())


def load(p):
    return json.loads(p.read_text())


input_record = load(REVIEW / "INPUT-HASH-CHECK.json")
assert all(sha(SEALED / x["path"]) == x["expected_sha256"] for x in input_record["files"])
freeze_path = BASE / "publication/PF03-LOCAL-EVIDENCE-FREEZE.json"
freeze = load(freeze_path)
assert sha(freeze_path) == "dc090fe6ccba8a12f344cb2392267a8f8ffad3be5cf1b552bb821e40fb0099d1"
assert all(sha(PUBLISH / name) == h for name, h in freeze["files"].items())

lean_sources = {str(p.relative_to(SEALED)): sha(p) for p in SEALED.rglob("*.lean")}
assert all(sha(PUBLISH / name) == h for name, h in lean_sources.items())
for name in ["NUMERICAL_TARGETS.md", "comparator.json", "STATEMENT-FREEZE.json"]:
    assert (SEALED / name).read_bytes() == (PUBLISH / name).read_bytes()

closure = set()
external = set()


def visit(module):
    p = PUBLISH / (module.replace(".", "/") + ".lean")
    if not p.exists():
        external.add(module)
        return
    if module in closure:
        return
    closure.add(module)
    for im in re.findall(r"^import ([A-Za-z0-9_.]+)\s*$", p.read_text(), re.M):
        visit(im)


visit("Solution")
assert len(closure) == 60 and "Challenge" not in closure
for m in closure:
    s = (PUBLISH / (m.replace(".", "/") + ".lean")).read_text()
    assert not re.search(r"\b(sorry|admit|axiom|native_decide|implemented_by|unsafe)\b|\[extern", s), m

audit_path = EVIDENCE / "LOCAL-REPLAY-AUDIT.json"
assert sha(audit_path) == "1656823e9c87a11fb434c20d167cc0635a38014940078795fc22fb98eab62137"
audit = load(audit_path)
receipts = {}
receipt_hash = {}
for run, r in audit["lossless_original_receipts"].items():
    gz = (EVIDENCE / r["file"]).read_bytes()
    b = gzip.decompress(gz)
    assert shab(gz) == r["gzip_sha256"] and shab(b) == r["original_sha256"]
    receipts[run] = json.loads(b)
    receipt_hash[run] = shab(b)
records = {r["module"]: r for r in audit["module_records"]}
assert set(records) == closure


def command(run, module):
    xs = [c for c in receipts[run]["commands"] if c["module"] == module]
    assert len(xs) == 1
    return xs[0]


total_reuse_links = 0
for m, r in records.items():
    assert sha(PUBLISH / r["source"]) == r["source_sha256"]
    fresh = command(r["fresh_success_run"], m)
    assert fresh == r["actual_fresh_command"]
    assert fresh["exit_code"] == 0 and fresh["source_sha256"] == r["source_sha256"]
    assert fresh["output_sha256"] == r["output_sha256"]
    assert sha(EVIDENCE / r["log"]) == fresh["log_sha256"]
    assert "--threads=1" in fresh["argv"] and "--memory=4096" in fresh["argv"]
    for dm, dh in fresh["dependency_olean_sha256"].items():
        assert records[dm]["output_sha256"] == dh
    last = "recovery-047"
    for link in r["reuse_chain"]:
        assert link["run"] == last
        c = command(link["run"], m)
        assert c["status"] == "reused_exact_successful_local_output"
        assert c["source_sha256"] == r["source_sha256"]
        assert c["output_sha256"] == r["output_sha256"]
        assert c["prior_receipt_sha256"] == link["prior_receipt_sha256"] == receipt_hash[link["prior"]]
        assert Path(c["prior_receipt"]).parent.name == link["prior"]
        assert all(sha(PUBLISH / n) == h for n, h in c["transitive_source_hashes"].items())
        last = link["prior"]
        total_reuse_links += 1
    assert last == r["fresh_success_run"]

cfg = load(PUBLISH / "comparator.json")
log = (EVIDENCE / records["Solution"]["log"]).read_text()
axioms = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log))
assert len(axioms) == 25 and set(axioms) == set(cfg["theorem_names"])
assert all(set(a.split(", ")) == set(cfg["permitted_axioms"]) for a in axioms.values())
assert cfg["definition_names"] == []
assert audit["aggregate_command"] == command("recovery-047", "Solution")

record = {
    "reviewer": "/root/recover_published_coverage",
    "scope": "Supplementary read-only authentication of existing records and source closure; no Lean or Comparator execution",
    "sealed_project_entries_rechecked": len(input_record["files"]),
    "publication_freeze_entries_rechecked": len(freeze["files"]),
    "all_publication_Lean_sources_unchanged": True,
    "frozen_numeric_and_comparator_bytes_unchanged": True,
    "solution_local_import_closure_count": len(closure),
    "challenge_reachable_from_solution": False,
    "static_forbidden_source_token_scan": "PASS (supplementary; not a proof-term axiom audit)",
    "existing_original_receipts_authenticated": len(receipts),
    "existing_module_fresh_successes_and_logs_authenticated": len(records),
    "existing_reuse_links_authenticated": total_reuse_links,
    "observed_final_contract_axiom_reports": len(axioms),
    "observed_axioms_for_each_contract": ["propext", "Classical.choice", "Quot.sound"],
    "Lean_or_Comparator_run_by_reviewer": False,
    "GitHub_Comparator": "UNRUN FOR THIS PACKAGE",
    "new_whole_target_count": 0,
    "publication_freeze_sha256": sha(freeze_path),
    "local_audit_sha256": sha(audit_path),
    "Solution_source_sha256": sha(PUBLISH / "Solution.lean"),
    "Solution_log_sha256": records["Solution"]["actual_fresh_command"]["log_sha256"],
    "closure_modules": sorted(closure),
    "script_sha256": sha(Path(__file__)),
}
(REVIEW / "EVIDENCE-CROSSCHECK.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps({k: v for k, v in record.items() if k != "closure_modules"}, indent=2))
