#!/usr/bin/env python3
"""Bind author final evidence and preserve the interrupted attempt without accepting it."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json

BASE = Path(__file__).resolve().parent
REPO = BASE.parents[5]
AUTHOR = REPO / "docs/lean/proofs/TR-04/campaign-2026-10-23/tt-dimension-author-2026-10-26"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
lock = json.loads((AUTHOR / "source-lock.json").read_text())
assert sha(AUTHOR / "source-lock.json") == "728737eeb3f3c75030b539e2d939f94bea2c0b18d986d8abf4550961e255fbea"
result = json.loads((AUTHOR / "final/result.json").read_text())
assert result["passed"] and sha(AUTHOR / "final/result.json") == "93f591d28774eb9ec6c4c2fa52b9a01a2d34e46e11e7a0c20939b14f0f99566b"
assert not (AUTHOR / "run/result.json").exists()
assert "KeyboardInterrupt" in (AUTHOR / "run/source-build.log").read_text()
expected = {r["path"].removeprefix("lean-statements/"): r["sha256"] for r in lock["project_closure"]}
for directory in ["run", "final"]:
    for name, digest in expected.items():
        p = AUTHOR / directory / "sources" / name
        assert p.is_file() and not p.is_symlink() and sha(p) == digest
artifacts = {}
for directory in [AUTHOR / "run", AUTHOR / "final"]:
    for p in sorted(directory.rglob("*")):
        if p.is_file() and p.suffix in {".lean", ".log", ".json"}:
            assert not p.is_symlink()
            artifacts[str(p.relative_to(REPO))] = sha(p)
for name in ["source-lock.json", "replay.py", "REPORT.md", "driver.log", "final-driver.log", "consumer-development.lean", "consumer-development.log"]:
    p = AUTHOR / name
    assert p.is_file() and not p.is_symlink()
    artifacts[str(p.relative_to(REPO))] = sha(p)
data = {
    "passed": True, "type": "author_artifact_history_hash_check_only",
    "executed_utc": datetime.now(timezone.utc).isoformat(),
    "checker_sha256": sha(Path(__file__)),
    "author_final_accepted_as_author_evidence_only": True,
    "interrupted_run_accepted": False,
    "interrupted_run_terminal_result_present": False,
    "interrupted_run_diagnostic": "KeyboardInterrupt retained in run/source-build.log; no terminal result exists. All 27 interrupted-attempt source snapshots remain byte-exact to the final frozen lock. No completion is inferred for that run.",
    "source_snapshot_count_each": len(expected), "artifact_hashes": artifacts,
    "fresh_Lean_replayed_by_this_check": False,
    "proof_inputs_changed": False, "full_TR04_Target_proved": False,
}
parser = argparse.ArgumentParser()
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()
args.output.write_text(json.dumps(data, indent=2) + "\n")
print(json.dumps({"passed": True, "artifacts": len(artifacts), "output_sha256": sha(args.output)}, indent=2))
