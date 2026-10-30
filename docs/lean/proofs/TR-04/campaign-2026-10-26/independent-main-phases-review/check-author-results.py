#!/usr/bin/env python3
"""Read-only binding of all three frozen terminal author replays and auditor controls."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json

BASE = Path(__file__).resolve().parent
REPO = BASE.parents[5]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
config = json.loads((BASE / "source-lock.json").read_text())
specs = {
    "startup": (BASE.parent / "tt-startup-author/result.json", "fade3d6df55347ebafdab97ac4c01a816f3252d9911f93ca89caaccdec7bd76f", BASE.parent / "tt-startup-author/sources"),
    "dispatch_metadata": (BASE.parent / "header-dispatch-metadata-author/run/result.json", "cab9bd18b4f62c5d0ce72f961710e8d0c0eeb541b1cf581144d9351a8821b822", BASE.parent / "header-dispatch-metadata-author/run/sources"),
    "first_selection": (BASE.parent / "first-selection-author/result.json", "1dfac3db26741bf98d00e40183fad1376d50739756061a7f4ba9ec71db5629aa", BASE.parent / "first-selection-author/sources"),
}
artifacts, terminal = {}, []


def bind(p, expected=None):
    assert p.is_file() and not p.is_symlink(), str(p)
    digest = sha(p)
    if expected is not None: assert digest == expected, str(p)
    artifacts[str(p.relative_to(REPO))] = digest
    return digest


for b in config["blocks"]:
    result_path, expected, snapshots = specs[b["key"]]
    bind(result_path, expected)
    d = json.loads(result_path.read_text())
    assert d.get("passed", d.get("success")) is True
    assert d["source_lock_sha256"] == b["author_lock_sha256"]
    assert d["project_objects_reused"] is False
    bind(REPO / b["author_lock_path"], b["author_lock_sha256"])
    for r in b["records"]:
        bind(snapshots / r["path"].removeprefix("lean-statements/"), r["sha256"])
    for name, digest in d.get("logs", {}).items(): bind(result_path.parent / name, digest)
    for item in d.get("evidence", []): bind(result_path.parent / item["path"], item["sha256"])
    for item in d.get("commands", []):
        assert item["exit_code"] == 0
        bind(Path(item["path"]), item["sha256"])
    terminal.append({"key": b["key"], "result": str(result_path.relative_to(REPO)), "sha256": expected, "terminal_author_passed": True, "accepted_as_independent_evidence": False})

fixture = BASE / "private-auditor-preflight-4"
control = json.loads((fixture / "result.json").read_text())
assert control["passed"] and control["driver_sha256"] == sha(BASE / "replay.py")
assert control["positive_private_local_public_passed"] and control["custom_axiom_hidden_in_private_theorem_rejected"]
assert not control["negative_control_accepted_as_a_proof"]
bind(fixture / "result.json")
for c in control["commands"]:
    bind(fixture / c["source"], c["source_sha256"])
    bind(REPO / c["log"], c["log_sha256"])
    assert c["exit_code"] == c["expected_exit_code"]
assert control["commands"][-1]["expected_exit_code"] == 1
for old_directory in ["private-auditor-preflight-3", "private-auditor-preflight-2", "private-auditor-preflight"]:
 for old in sorted((BASE / old_directory).iterdir()):
  if old.is_file(): bind(old)
for p in sorted((BASE / "private-auditor-preflight").iterdir()):
    if p.is_file(): bind(p)
for n in ["replay-before-hygiene-correction.py", "make-replay-before-hygiene-correction.py", "check-private-auditor-before-hygiene-correction.py", "private-auditor-hygiene-diagnostic.json", "private-name-provenance.json"]:
    bind(BASE / n)
assert "unknown trust class" in (BASE / "private-auditor-preflight/PrivatePositive.lean.log").read_text()

for old_name in ["replay-attempt-1.py", "make-replay-attempt-1.py", "check-private-auditor-attempt-1.py", "check-author-results-attempt-1.py", "author-and-control-receipts-attempt-1.json", "author-and-control-receipts-local-context-development.json"]:bind(BASE / old_name)

data = {"passed": True, "executed_utc": datetime.now(timezone.utc).isoformat(), "checker_sha256": sha(Path(__file__)),
    "scope": "Author terminal receipts and exact auditor positive/negative controls only; the independent Lean replay has its own result.",
    "terminal_author_results": terminal, "artifact_hashes": artifacts,
    "private_auditor_positive_and_negative_passed": True,
    "initial_auditor_hygiene_development_failure_accepted": False,
    "negative_custom_axiom_fixture_accepted_as_proof": False,
    "proof_inputs_changed": False, "full_TR04_Target_proved": False}
parser = argparse.ArgumentParser()
parser.add_argument("--output", required=True, type=Path)
args = parser.parse_args()
args.output.write_text(json.dumps(data, indent=2) + "\n")
print(json.dumps({"passed": True, "terminal_author_scopes": len(terminal), "bound_artifacts": len(artifacts), "output_sha256": sha(args.output)}, indent=2))
