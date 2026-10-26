#!/usr/bin/env python3
"""Reproduce the fixed published Solved/proof-source inventory, read-only.

Only this directory's inventory.json is written. Git objects, not checkout
contents, define published and candidate truth; source presence is not proof.
"""
from __future__ import annotations

import collections
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = next(p for p in Path(__file__).resolve().parents if (p / ".git").exists())
OUT = Path(__file__).resolve().parent
PUBLISHED = "5487945e5a72abd952b0c89915915de8cc9b3e65"
PREVIOUS = "47006df8b3a6c724a557266c891893d03e69323a"
CANDIDATES = {
    "PF-05": ("codex/pf05-lean-proof", "6e2c960557b6f61af1ed6e679b0634dd498181b2"),
    "TR-14": ("codex/tr14-proof-gap-2026-10-16", "fdb40b66425ec58e4806cee93d2aaf92a0f8597c"),
    "RA-19": ("codex/ra19-lean-proof", "0b5ac28a922c8c8768dfe043a6e282cd190bcfe8"),
    "TR-06": ("codex/tr06-formal-verification", "50e97f90c11a65028500cb1dcd840c1de0bb314b"),
}
PARTIAL_IDS = {"IE-21", "IE-22", "IV-02", "IV-04", "MD-06", "TR-04", "TR-14", "SP-14"}


def git(*args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=ROOT)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read(commit: str, path: str) -> bytes:
    return git("show", f"{commit}:{path}")


def tree(commit: str) -> set[str]:
    return set(git("ls-tree", "-r", "--name-only", commit).decode().splitlines())


def live(path: str) -> bool:
    return path.endswith(".lean") and not any(
        part in {"reviews", "verification", "archive", "archives", ".lake"}
        for part in Path(path).parts
    )


def status(data: bytes) -> str:
    match = re.search(r"^\*\*Status:\*\*\s*(.*)$", data.decode(), re.M)
    return match.group(1).strip() if match else "MISSING"


def inspect(commit: str) -> dict:
    paths = tree(commit)
    registry_data = read(commit, "problem_ids.json")
    registry = json.loads(registry_data)
    entries = []
    for ident, canonical in registry.items():
        data = read(commit, canonical)
        entry = {
            "id": ident, "canonical_path": canonical,
            "canonical_sha256": sha(data), "status": status(data),
            "title": data.decode().splitlines()[0].removeprefix("# "),
        }
        if entry["status"] == "Solved":
            prefixes = [str(Path(canonical).parent / "lean") + "/",
                        f"lean-statements/NLA/Proofs/{ident.replace('-', '')}/"]
            entry["live_source_hashes"] = {
                p: sha(read(commit, p)) for p in sorted(paths)
                if live(p) and any(p.startswith(prefix) for prefix in prefixes)
            }
            entry["source_classification"] = (
                "partial-project-not-full-target" if ident in PARTIAL_IDS
                else "statement-or-informal-proof-only"
            )
            contract_paths = [
                f"lean-statements/NLA/Statements/{ident.replace('-', '')}.lean",
                f"docs/lean/statements/{ident}/ORIGINAL.md",
                f"docs/lean/statements/{ident}/statement.json",
            ]
            entry["contract_hashes"] = {p: sha(read(commit, p)) for p in contract_paths if p in paths}
        entries.append(entry)
    solved = [e for e in entries if e["status"] == "Solved"]
    return {
        "commit": commit, "registry_sha256": sha(registry_data),
        "registered_count": len(registry),
        "status_counts": dict(sorted(collections.Counter(e["status"] for e in entries).items())),
        "solved_ids": [e["id"] for e in solved],
        "partial_solved_ids": [e["id"] for e in solved if e["id"] in PARTIAL_IDS],
        "statement_only_solved_ids": [e["id"] for e in solved if e["id"] not in PARTIAL_IDS],
        "entries": entries,
    }


def main() -> None:
    before = git("status", "--short").decode().splitlines()
    published = inspect(PUBLISHED)
    previous_registry = json.loads(read(PREVIOUS, "problem_ids.json"))
    current_registry = json.loads(read(PUBLISHED, "problem_ids.json"))
    candidate_reports = []
    for ident, (ref, fixed_commit) in CANDIDATES.items():
        commit = fixed_commit or git("rev-parse", ref).decode().strip()
        paths = tree(commit)
        canonical = current_registry[ident]
        prefixes = [str(Path(canonical).parent / "lean") + "/",
                    f"lean-statements/NLA/Proofs/{ident.replace('-', '')}/"]
        sources = sorted(p for p in paths if live(p) and any(p.startswith(x) for x in prefixes))
        candidate_reports.append({
            "id": ident, "ref_label": ref, "commit": commit,
            "canonical_status": status(read(commit, canonical)),
            "live_source_hashes": {p: sha(read(commit, p)) for p in sources},
            "live_source_count": len(sources),
            "canonical_solution_exists": str(Path(canonical).parent / "lean/Solution.lean") in paths,
            "verification_in_this_inventory": "not-run",
        })
    report = {
        "schema_version": 1, "audit_date": "2026-10-23",
        "method": "Read canonical problem_ids.json at immutable published commit; ignore historical/review/verification copies as live sources.",
        "scope_limit": "Source inventory only; no new theorem-truth, fidelity, kernel, CI or Comparator verification claim.",
        "working_head": git("rev-parse", "HEAD").decode().strip(),
        "locally_available_origin_main": git("rev-parse", "origin/main").decode().strip(),
        "worktree_status_before_report": before,
        "published": published,
        "previous_audit_base": PREVIOUS,
        "registered_pairs_preserved_from_previous_audit": all(current_registry.get(k) == v for k, v in previous_registry.items()),
        "registry_equal_to_previous_audit": current_registry == previous_registry,
        "later_candidates": candidate_reports,
        "existing_sp11_completion": {
            "checked_commit": "9264361fafb89b37b5c48236afebb304bc84110a",
            "workflow_run": "39131755109", "job": "117688269984",
            "artifact_id": "12138590670",
            "inspected_source_hashes": {
                p: sha(read(PUBLISHED, p)) for p in [
                    "docs/lean/proofs/SP-11/LINUX_CI_RECEIPT.md",
                    "docs/lean/proofs/SP-11/README.md",
                    "eigenvalues-and-inverse-problems/SP-11/lean/Solution.lean",
                    "eigenvalues-and-inverse-problems/SP-11/README.md",
                ]
            },
            "changed_project_paths_since_checked_commit": git(
                "diff", "--name-only", "9264361fafb89b37b5c48236afebb304bc84110a",
                PUBLISHED, "--", "eigenvalues-and-inverse-problems/SP-11/lean"
            ).decode().splitlines(),
            "artifact_or_kernel_replay_in_this_inventory": "not-run",
        },
    }
    (OUT / "inventory.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"published": PUBLISHED, "counts": published["status_counts"],
                      "solved": len(published["solved_ids"]),
                      "partial": len(published["partial_solved_ids"]),
                      "statement_only": len(published["statement_only_solved_ids"]),
                      "candidate_source_counts": {x["id"]: x["live_source_count"] for x in candidate_reports}}, indent=2))


if __name__ == "__main__":
    main()
