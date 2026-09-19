"""Read-only replay of this statement review's bindings and header evidence.

This does not execute Lean, Comparator, the author's generator, or the numerical
preflight. The separately recorded preflight and root compiler runs are evidence
being checked; replaying this file does not create another proof execution.
"""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    manifest = json.loads((HERE / "MANIFEST.json").read_text())
    assert manifest["verdict"] == "APPROVE_EXACT_STATEMENTS_ONLY"
    for rel, expected in manifest["review_payload_hashes"].items():
        assert sha(HERE / rel) == expected, rel
    candidate = Path(manifest["candidate"])
    for rel, expected in manifest["approved_sources"].items():
        assert sha(candidate / rel) == expected, rel
    evidence = json.loads((HERE / "HEADER-EVIDENCE-BINDINGS.json").read_text())
    for row in evidence["bindings"]:
        assert sha(HERE / row["file"]) == row["sha256"], row["file"]
    packet = json.loads((HERE / "header-evidence/SUCCESSFUL-HEADER-PACKET.json").read_text())
    assert packet["sources"] == manifest["approved_sources"]
    receipt = json.loads((HERE / "header-evidence/RECEIPT-recovery015.json").read_text())
    assert receipt.get("end")
    by = {x["module"]: x for x in receipt["commands"]}
    prior = json.loads((HERE / "header-evidence/RECEIPT-recovery013.json").read_text())
    for cmd in packet["actual_commands"]:
        assert by[cmd["module"]] == cmd
        if cmd.get("status") == "reused_exact_successful_local_output":
            old = next(x for x in prior["commands"] if x["module"] == cmd["module"])
            assert old["exit_code"] == 0
            assert old["source_sha256"] == cmd["source_sha256"]
            assert old["output_sha256"] == cmd["output_sha256"]
        else:
            assert cmd["exit_code"] == 0 and cmd.get("end")
            assert "--threads=1" in cmd["argv"] and "--memory=4096" in cmd["argv"]
            log = HERE / "header-evidence" / (cmd["module"] + ".log")
            assert sha(log) == cmd["log_sha256"]
    challenge = (candidate / "Challenge.lean").read_text()
    assert challenge.count("  sorry\n") == 25
    log = (HERE / "header-evidence/PF03Challenge.log").read_text().splitlines()
    assert len(log) == 25 and all("warning: declaration uses `sorry`" in line for line in log)
    numerical = json.loads((HERE / "INDEPENDENT-PREFLIGHT-final.json").read_text())
    assert numerical["sources"] == manifest["approved_sources"]
    assert numerical["checks"]["strict_cross_pairings"] == 189
    assert numerical["checks"]["strict_positive_rational_slice_pairings"] == 21
    assert numerical["Lean_Lake_Comparator_or_author_generator_executed"] is False
    print(json.dumps({
        "scope": "Review payload/current-source hashes and recorded successful header evidence only",
        "result": "PASS",
        "verdict": manifest["verdict"],
        "contracts": 25,
        "Lean_Lake_Comparator_or_author_generator_executed": False,
        "whole_problem_verified": False,
        "count_change": 0,
    }, indent=2))


if __name__ == "__main__":
    main()
