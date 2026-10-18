#!/usr/bin/env python3
"""Read-only canonical-registry inventory; writes only this report directory.

Run from any checkout of this repository. Published refs are frozen before
inspection. Source presence is never treated as proof verification.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
from pathlib import Path
import re
import subprocess


ROOT = next(parent for parent in Path(__file__).resolve().parents if (parent / ".git").exists())
OUT = Path(__file__).resolve().parent
PUBLISHED = "47006df8b3a6c724a557266c891893d03e69323a"
CANDIDATES = {
    "RA-10": ("codex/ra10-proof-verification", "466a178a0f9ada18c054fdfd8db38e3d2a999ec7"),
    "MD-03": ("codex/md03-lean-verification", "fb7acabd62df62b20e2813165773a2602ac9eac0"),
    "MD-04": ("codex/md04-lean-verification", "d9212bc43ce51a3ccdb376aa661b11d3d41f49f8"),
    "PF-05": ("codex/pf05-lean-proof", "6e2c960557b6f61af1ed6e679b0634dd498181b2"),
    "RA-19": ("codex/ra19-lean-proof", "0b5ac28a922c8c8768dfe043a6e282cd190bcfe8"),
    "TR-14": ("codex/tr14-proof-gap-2026-10-16", "fdb40b66425ec58e4806cee93d2aaf92a0f8597c"),
}


def git(*args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=ROOT)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_at(commit: str | None, path: str) -> bytes:
    return git("show", f"{commit}:{path}") if commit else (ROOT / path).read_bytes()


def paths_at(commit: str | None) -> set[str]:
    if commit:
        return set(git("ls-tree", "-r", "--name-only", commit).decode().splitlines())
    # Git's tracked and untracked inventory avoids dependency/build directories.
    return set(git("ls-files", "--cached", "--others", "--exclude-standard").decode().splitlines())


def live_source(path: str) -> bool:
    return path.endswith(".lean") and not any(
        part in {"reviews", "verification", "archive", "archives", ".lake"}
        for part in Path(path).parts
    )


def inspect(commit: str | None) -> dict:
    paths = paths_at(commit)
    registry_bytes = read_at(commit, "problem_ids.json")
    registry = json.loads(registry_bytes)
    entries = []
    for ident, path in registry.items():
        data = read_at(commit, path)
        text = data.decode()
        status_match = re.search(r"^\*\*Status:\*\*\s*(.*)$", text, re.M)
        status = status_match.group(1).strip() if status_match else "MISSING"
        project = str(Path(path).parent / "lean")
        source_paths = sorted(p for p in paths if p.startswith(project + "/") and live_source(p))
        shared_prefix = f"lean-statements/NLA/Proofs/{ident.replace('-', '')}/"
        shared_sources = sorted(p for p in paths if p.startswith(shared_prefix) and live_source(p))
        statement = f"lean-statements/NLA/Statements/{ident.replace('-', '')}.lean"
        original = f"docs/lean/statements/{ident}/ORIGINAL.md"
        metadata = f"docs/lean/statements/{ident}/statement.json"
        entry = {
            "id": ident,
            "canonical_path": path,
            "canonical_sha256": sha(data),
            "title": text.splitlines()[0].removeprefix("# "),
            "status": status,
            "canonical_lean_sources": {p: sha(read_at(commit, p)) for p in source_paths},
            "shared_proof_sources": {p: sha(read_at(commit, p)) for p in shared_sources},
            "source_presence_is_proof_verification": False,
        }
        for key, p in [("shared_statement", statement), ("preserved_original", original), ("statement_metadata", metadata)]:
            if p in paths:
                entry[key] = {"path": p, "sha256": sha(read_at(commit, p))}
        if status == "Solved":
            entry["requires_full_target_verification"] = True
            entry["source_classification"] = (
                "unpromoted-canonical-project" if source_paths else
                "partial-shared-proof" if shared_sources else "statement-or-mathematical-source-only"
            )
        entries.append(entry)
    counts = dict(sorted(collections.Counter(e["status"] for e in entries).items()))
    solved = [e for e in entries if e["status"] == "Solved"]
    return {
        "commit": commit,
        "registry_sha256": sha(registry_bytes),
        "registered_count": len(registry),
        "status_counts": counts,
        "solved_ids": [e["id"] for e in solved],
        "solved_count": len(solved),
        "solved_without_canonical_lean_sources": [e["id"] for e in solved if not e["canonical_lean_sources"]],
        "solved_without_live_proof_sources": [e["id"] for e in solved if not e["canonical_lean_sources"] and not e["shared_proof_sources"]],
        "entries": entries,
    }


def main() -> None:
    global ROOT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--working-root", type=Path, default=ROOT, help="Checkout whose current working tree is inspected")
    parser.add_argument("--output", type=Path, default=OUT / "inventory-current.json", help="New report destination; the retained initial inventory.json is not overwritten by default")
    args = parser.parse_args()
    ROOT = args.working_root.resolve()
    working = inspect(None)
    published = inspect(PUBLISHED)
    wr = {e["id"]: e for e in working["entries"]}
    pr = {e["id"]: e for e in published["entries"]}
    transitions = [
        {"id": ident, "working_status": wr[ident]["status"], "published_status": e["status"]}
        for ident, e in pr.items() if wr[ident]["status"] != e["status"]
    ]
    candidate_reports = []
    for ident, (ref, commit) in CANDIDATES.items():
        paths = paths_at(commit)
        path = pr[ident]["canonical_path"]
        text = read_at(commit, path).decode()
        changes = git("diff", "--name-only", f"{PUBLISHED}...{commit}").decode().splitlines()
        candidate_reports.append({
            "id": ident, "ref_label": ref, "commit": commit,
            "canonical_status": re.search(r"^\*\*Status:\*\*\s*(.*)$", text, re.M).group(1).strip(),
            "canonical_path": path, "canonical_sha256": sha(text.encode()),
            "changed_paths_from_published_merge_base": changes,
            "new_lean_source_hashes": {
                p: sha(read_at(commit, p)) for p in changes if p in paths and live_source(p)
            },
            "verification_in_this_inventory": "not-run",
        })
    report = {
        "schema_version": 1,
        "audit_date": "2026-10-17",
        "method": "Canonical problem_ids.json entries only; read git objects without checkout; ignore review/archive copies as live proofs.",
        "scope_limit": "This is a source and status audit. It does not establish theorem truth, signature fidelity, build success or Comparator acceptance.",
        "working_head": git("rev-parse", "HEAD").decode().strip(),
        "worktree_status_at_inventory": git("status", "--short").decode().splitlines(),
        "working": working,
        "published": published,
        "status_transitions": transitions,
        "later_candidates": candidate_reports,
    }
    OUT.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "working_status_counts": working["status_counts"],
        "published_status_counts": published["status_counts"],
        "working_solved": working["solved_count"],
        "published_solved": published["solved_count"],
        "status_transitions": len(transitions),
        "later_candidates": len(candidate_reports),
    }, indent=2))


if __name__ == "__main__":
    main()
