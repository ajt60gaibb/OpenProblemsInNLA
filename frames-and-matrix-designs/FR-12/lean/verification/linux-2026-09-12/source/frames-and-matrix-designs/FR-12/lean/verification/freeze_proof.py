"""Freeze the completed author's proof; independent final reviews and Linux are pending."""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess

OUT = Path(__file__).resolve().parent
PROJECT = OUT.parent
REPO = PROJECT.parents[2]

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

statement_path = PROJECT / "reviews/statement-freeze.json"
assert sha(statement_path) == "5fbbcbce16da324a186dd765d120c883e4800efe2e491fbf069c9f7c74f5372c"
statement = json.loads(statement_path.read_text())
for name, digest in statement["files"].items():
    assert sha(PROJECT/name) == digest, name
for name, digest in statement["source_files"].items():
    assert sha(REPO/name) == digest, name
    assert (REPO/name).read_bytes() == subprocess.check_output(
        ["git", "show", statement["base_commit"] + ":" + name], cwd=REPO)

gate = json.loads((OUT/"proof-start.json").read_text())
for name, digest in gate["statement_approvals_sha256"].items():
    assert sha(PROJECT/name) == digest, name
fresh = json.loads((OUT/"fresh-checks.json").read_text())
assert len(fresh["commands"]) == 8
assert all(x["exit_code"] == 0 for x in fresh["commands"])
for command in fresh["commands"]:
    assert sha(PROJECT/command["source"]) == command["source_sha256"]
    assert sha(OUT/command["log"]) == command["log_sha256"]
axioms = json.loads((OUT/"axioms.json").read_text())
assert len(axioms["reports"]) == 14
assert all(set(x["axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
           for x in axioms["reports"])
assert json.loads((OUT/"proof-build.json").read_text())["exit_code"] == 0
assert "warning:" not in (OUT/"proof-build.log").read_text()
assert "2157 jobs" in (OUT/"proof-build.log").read_text()

names = subprocess.check_output(
    ["git", "ls-files", "--cached", "--others", "--exclude-standard", "--", "."],
    cwd=PROJECT, text=True).splitlines()
excluded = {"reviews/proof-freeze.json", "reviews/proof-completion.md"}
files = {}
for name in sorted(set(names) - excluded):
    assert not any(p in {".lake", ".verification", "__pycache__"} for p in Path(name).parts)
    assert not name.endswith((".olean", ".ilean", ".o", ".so", ".dylib"))
    files[name] = sha(PROJECT/name)

record = {
    "stage": "Complete author proof frozen; two independent final reviews and Linux pending",
    "date_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "base_commit": statement["base_commit"], "branch": statement["branch"],
    "files": files, "source_files": statement["source_files"],
    "statement_freeze_sha256": sha(statement_path),
    "statement_reviews": gate["statement_approvals_sha256"],
    "all_19_statement_inputs_unchanged": True,
    "all_configuration_and_dependency_pins_unchanged": True,
    "public_signature_note": "All seven source signatures match after alpha-renaming the unused local forall binder hn to _hn in Solution counting_semantics; the frozen Challenge is byte-identical. The Solution lower-bound comment correctly distinguishes the inner natural exponent from the outer real exponent.",
    "exports": json.loads((PROJECT/"comparator.json").read_text())["theorem_names"],
    "build_reported_jobs": 2157, "fresh_commands": 8, "kernel_axiom_checks": 14,
    "LeanCert_role": "Actual explicit kernel trust audit of exact counting, algebra and real-power arguments; no interval certificate or native execution.",
    "independent_final_reviews": "pending", "Linux_Comparator": "pending",
    "readme_phase": "The historical statement-stage README remains frozen; update its present-tense status with an archived historical copy during candidate packaging."
}
(PROJECT/"reviews/proof-freeze.json").write_text(json.dumps(record, indent=2)+"\n")
print(json.dumps({"status": "Author proof frozen for independent final review",
                  "files": len(files), "original_sources": len(record["source_files"]),
                  "freeze_sha256": sha(PROJECT/"reviews/proof-freeze.json")}))
