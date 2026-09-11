#!/usr/bin/env python3
"""Check the packaged IE-05 sources, target preservation and dated fingerprints.

Run in a Git clone with the recorded accepted-base commit. This read-only check
binds the shipped artifacts; a later rebuild may change PDF metadata and should
receive its own dated verification record.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REFERENCE = HERE.parent
PROBLEM = ROOT / "linear-systems-and-elimination/IE-05"
BASE = "87366c62d3b5c47d170f747b1cb40ab38d501013"


def original(path):
    return subprocess.check_output(["git", "-C", str(ROOT), "show", BASE + ":" + path])


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def main():
    manifest = json.loads((HERE / "document-checks.json").read_text())
    for path, fingerprint in manifest["files"].items():
        data = (ROOT / path).read_bytes()
        assert len(data) == fingerprint["bytes"], path + ": byte count"
        assert sha256(data) == fingerprint["sha256"], path + ": SHA-256"

    recovery_manifest = manifest
    if "final_layout_and_eligibility" in manifest:
        prior_bytes = (HERE / "document-checks-before-layout-move.json").read_bytes()
        assert sha256(prior_bytes) == manifest["final_layout_and_eligibility"]["prior_document_manifest_sha256"]
        recovery_manifest = json.loads(prior_bytes)
        reference_readme = str((REFERENCE / "README.md").relative_to(ROOT))
        old_readme = recovery_manifest["files"][reference_readme]
        prefix = (REFERENCE / "README.md").read_bytes()[:old_readme["bytes"]]
        assert sha256(prefix) == old_readme["sha256"], "pre-layout reference text changed"
        layout = json.loads(subprocess.check_output(["python3", str(HERE / "check_layout_move.py")]))
        assert layout == json.loads((HERE / "layout-move-check.json").read_text())
        assert layout["verdict"] == "PASS"

    if "later_recovery_comparison" in manifest:
        previous_bytes = (HERE / "document-checks-before-recovery.json").read_bytes()
        assert sha256(previous_bytes) == manifest["later_recovery_comparison"]["prior_document_manifest_sha256"]
        previous = json.loads(previous_bytes)
        reference_readme = str((REFERENCE / "README.md").relative_to(ROOT))
        old_readme = previous["files"][reference_readme]
        prefix = (REFERENCE / "README.md").read_bytes()[:old_readme["bytes"]]
        assert sha256(prefix) == old_readme["sha256"], "pre-recovery reference text changed"
        for name in ["README.md", "solution.md", "solution.tex", "solution.pdf", "problem.tex", "problem.pdf"]:
            path = str((PROBLEM / name).relative_to(ROOT))
            assert recovery_manifest["files"][path] == previous["files"][path], "recovery changed publication artifact"

    frozen = (REFERENCE / "full-proof.md").read_text()
    assert sha256(frozen.encode()) == "18d49f30a3ef26f4c88a85c8ea1fc9e5c4e1702b4be6061d39aec892e96a4af7"
    solution = (PROBLEM / "solution.md").read_text()
    assert solution.count("\\nopagebreak[4]\n\n") == 23
    proof = solution[solution.index("## Theorem\n"):].replace("\\nopagebreak[4]\n\n", "")
    assert proof == frozen[frozen.index("## Theorem\n"):], "theorem/proof/scope changed"
    marker = b"## Context and notation\n"
    canonical = (PROBLEM / "README.md").read_bytes()
    before = original("linear-systems-and-elimination/IE-05/README.md")
    assert canonical[canonical.index(marker):] == before[before.index(marker):]
    assert b"**Status:** Solved" in canonical

    registry_bytes = (ROOT / "problem_ids.json").read_bytes()
    assert registry_bytes == original("problem_ids.json")
    registry = json.loads(registry_bytes)
    assert len(registry) == 203
    for identifier, path in registry.items():
        if identifier != "IE-05":
            assert (ROOT / path).read_bytes() == original(path), identifier + ": other canonical page"

    resolved = (ROOT / "RESOLVED.md").read_text()
    added = re.compile(r"^### ✅ IE-05 .*?(?=^### |\Z)", re.M | re.S)
    assert len(added.findall(resolved)) == 1
    assert added.sub("", resolved).encode() == original("RESOLVED.md")
    assert (ROOT / "references/README.md").read_bytes().startswith(original("references/README.md"))

    markdowns = list(REFERENCE.rglob("*.md")) + [PROBLEM / "README.md", PROBLEM / "solution.md"]
    links = 0
    for path in markdowns:
        for target in re.findall(r"\]\(([^)]+)\)", path.read_text()):
            target = target.split("#", 1)[0]
            if target and not re.match(r"[a-z]+:", target):
                assert (path.parent / target).exists(), str(path) + ": missing " + target
                links += 1

    email = re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}")
    own_files = [p for p in REFERENCE.rglob("*") if p.is_file()] + list(PROBLEM.glob("solution.*")) + [PROBLEM / "README.md", PROBLEM / "problem.tex"]
    for path in own_files:
        if path.suffix not in {".pdf", ".pyc"}:
            assert not email.search(path.read_text()), str(path) + ": unexpected contact email"

    print("PASS: unchanged complete reviewed proof and original target; 203 IDs; 202 other canonical pages;")
    print("all packaged fingerprints; original resolution entries and references preserved;", links, "local links; no contact email.")


if __name__ == "__main__":
    main()
