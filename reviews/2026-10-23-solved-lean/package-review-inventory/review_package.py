#!/usr/bin/env python3
"""Read-only assembly review checks; writes evidence outside staged package."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument("package", type=Path)
args = parser.parse_args()
package = args.package.resolve()
out = Path(__file__).resolve().parents[1]
repository = next(p for p in out.parents if (p / ".git").exists())
published = "5487945e5a72abd952b0c89915915de8cc9b3e65"


def digest(data):
    return hashlib.sha256(data).hexdigest()


paths = list(package.rglob("*"))
assert not any(p.is_symlink() for p in paths)
files = {p.relative_to(package).as_posix(): p.read_bytes() for p in paths if p.is_file()}
lock = json.loads(files["PACKAGE_LOCK.json"])
assert lock["published_base"] == published
assert set(files) == set(lock["files"]) | {"PACKAGE_LOCK.json"}
assert all(digest(files[p]) == record["sha256"] and len(files[p]) == record["bytes"]
           for p, record in lock["files"].items())

published_pairs = {
    "NLA/Statements/Infrastructure.lean": "lean-statements/NLA/Statements/Infrastructure.lean",
    "NLA/Statements/RA05.lean": "lean-statements/NLA/Statements/RA05.lean",
    "NLA/Statements/RA06.lean": "lean-statements/NLA/Statements/RA06.lean",
    "Reviewed/RA05.lean": "lean-statements/Reviewed/RA05.lean",
    "sources/ORIGINAL.md": "docs/lean/statements/RA-05/ORIGINAL.md",
    "sources/NUMERICAL_TARGETS.md": "docs/lean/statements/RA-05/NUMERICAL_TARGETS.md",
    "sources/part-1.tex": "references/holden-further-2026-09-14/RA-05/part-1.tex",
    "sources/part-2.tex": "references/holden-further-2026-09-14/RA-05/part-2.tex",
    "lean-toolchain": "lean-statements/lean-toolchain",
}
provenance = []
for destination, origin in published_pairs.items():
    data = subprocess.check_output(["git", "show", f"{published}:{origin}"], cwd=repository)
    assert data == files[destination]
    provenance.append({"destination": destination, "published_source": origin,
                       "sha256": digest(data), "equal": True})
canonical = subprocess.check_output(["git", "show", f"{published}:randomized-and-low-rank-approximation/RA-05/README.md"], cwd=repository)
assert canonical == files["sources/ORIGINAL.md"] and b"**Status:** Solved" in canonical
manifest = json.loads(files["lake-manifest.json"])
old_manifest = json.loads(subprocess.check_output(["git", "show", f"{published}:lean-statements/lake-manifest.json"], cwd=repository))
assert manifest["name"] == "NLARA05Support"
assert {k: v for k, v in manifest.items() if k != "name"} == {k: v for k, v in old_manifest.items() if k != "name"}

approved = {
    "NLA/Proofs/RA05/SupportMinimum.lean": ("ra05-minimum", "d21474d121f82481cf7de107ecaa8405d0b2d12cf60c08ef75fcbea471c1f0ce"),
    "NLA/Proofs/RA05/HyperplaneDefinitions.lean": ("ra05", "03c589f029a146203487f4d5ed5982eb67e4a91d64c0ab8f817baf1de898a276"),
    "NLA/Proofs/RA05/HyperplaneBridge.lean": ("ra05", "2e8d441f6aa46d7344c37762010be9e1afb30574e085bad980bb9bf01e7ccae1"),
}
for path, (packet, expected_hash) in approved.items():
    assert digest(files[path]) == expected_hash and files[path] == (out / packet / path).read_bytes()


def headers(data):
    return [" ".join(x.split()) for x in re.findall(r"(?ms)^theorem (.*?) := by", data.decode())]


minimum_headers = headers((out / "ra05-minimum/Challenge.lean").read_bytes())
hyperplane_headers = headers((out / "ra05/Challenge.lean").read_bytes())
assert len(minimum_headers) == 8 and len(hyperplane_headers) == 3
assert headers(files["Challenge.lean"]) == minimum_headers + hyperplane_headers
expected_names = ["NLA.Proofs.RA05.SupportMinimum." + x.split()[0] for x in minimum_headers]
expected_names += ["NLA.Proofs.RA05." + x.split()[0] for x in hyperplane_headers]
config = json.loads(files["comparator.json"])
metadata = json.loads(files["formalization.yaml"])
assert config["theorem_names"] == expected_names and len(set(expected_names)) == 11
assert config["definition_names"] == []
assert set(config["permitted_axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
assert config["challenge_module"] == "Challenge" and config["solution_module"] == "Solution"
assert [r["declaration"] for r in metadata["status"]["main_results"]] == expected_names
assert metadata["status"]["whole_problem_verified"] is False
assert metadata["status"]["canonical_status"] == "Solved"
for prefix in ("#assert_trust kernel ", "#print axioms "):
    selected = re.findall(r"^" + re.escape(prefix) + r"(.+)$", files["SupportAudit.lean"].decode(), re.M)
    assert len(selected) == 11 and set(selected) == set(expected_names)
assert "import Challenge" not in files["Solution.lean"].decode()

replay_path = out / "package-review-inventory/replay/result.json"
replay = json.loads(replay_path.read_text())
assert replay["pass"] and len(replay["commands"]) == 11
assert all(c["exit_code"] == 0 and c["source_sha256"] == digest(files[c["source"]]) for c in replay["commands"])
assert replay["dependencies_before"] == replay["dependencies_after"]
assert len(replay["dependencies_before"]) == 10
assert all(d["revision"] == d["expected_revision"] and d["tracked_status"] == "" for d in replay["dependencies_before"])
audit = (replay_path.parent / "SupportAudit.lean.log").read_text()
axiom_lists = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", audit)
assert len(axiom_lists) == 11
assert all({a.strip() for a in axioms.split(",")} == {"propext", "Classical.choice", "Quot.sound"} for axioms in axiom_lists)
report = {
    "reviewer": "/root/inventory", "published_base": published,
    "staged_package": str(package), "stage_written_by_review": False,
    "file_count_including_lock": len(files), "package_lock_complete_and_matching": True,
    "no_symlinks": True, "input_sha256": {p: digest(b) for p, b in sorted(files.items())},
    "published_copies": provenance, "original_matches_canonical_and_preserved_original": True,
    "dependency_manifest_changes_only_root_name": True,
    "approved_proofs_equal": {p: {"packet": a[0], "sha256": a[1]} for p, a in approved.items()},
    "exact_challenge_and_metadata_and_audit_coverage": expected_names,
    "whole_problem_verified": False, "canonical_status": "Solved",
    "independent_local_replay_result_sha256": digest(replay_path.read_bytes()),
    "local_source_commands_passed": 11, "permitted_axiom_reports_passed": 11,
    "dependencies_pinned_and_tracked_clean_before_after": 10,
    "linux_ci_or_comparator_acceptance_claimed_by_this_review": False,
    "passed": True,
}
(out / "PACKAGE_REVIEW_INVENTORY_INPUTS.json").write_text(json.dumps(report, indent=2) + "\n")
print("Package assembly and independent source replay review: PASS (11 support exports)")
