#!/usr/bin/env python3
"""Check the byte-identical RA-06 frozen statement and proof import closure."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


PINNED_LOCK_SHA256 = "0e848a584c74e394ba65c41e6ffd708a47b3f11d4c636779efd7197562818d3f"
PINNED_FINAL_SHA256 = "54454fd6207fb55664d06d8c32ee9608c5089db08efa34d2d90716966c8b434c"
MODULE_ROOT = Path("NLA")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate RA-06 source-lock key: {key}")
        result[key] = value
    return result


def validate_ra06_source_lock(project: Path) -> None:
    """Reject missing, changed, symlinked, or extra copied NLA modules."""
    lockfile = project / "ra06-source-lock.json"
    if not lockfile.is_file() or lockfile.is_symlink() or sha256(lockfile) != PINNED_LOCK_SHA256:
        raise ValueError("RA-06 source lock is absent or changed")
    lock = json.loads(lockfile.read_text(), object_pairs_hook=_unique_pairs)
    if (lock.get("schema_version") != 1 or lock.get("canonical_problem") != "RA-06"
            or lock.get("frozen_target") != "NLA.Statements.RA06.Target"
            or lock.get("proved_source_theorem") != "NLA.Proofs.RA06.target"):
        raise ValueError("RA-06 source lock has incorrect target provenance")
    entries = lock.get("files")
    if not isinstance(entries, list) or len(entries) != 16:
        raise ValueError("RA-06 source lock must contain the 16-file import closure")
    expected = {}
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != {"source", "path", "sha256"}:
            raise ValueError("malformed RA-06 source-lock entry")
        name, source, digest = entry["path"], entry["source"], entry["sha256"]
        if (not isinstance(name, str) or not isinstance(source, str)
                or not isinstance(digest, str) or source != "lean-statements/" + name
                or not name.startswith("NLA/") or ".." in Path(name).parts
                or not name.endswith(".lean") or name in expected):
            raise ValueError("invalid or duplicate RA-06 source-lock path")
        expected[name] = digest
    if expected.get("NLA/Proofs/RA06/Final.lean") != PINNED_FINAL_SHA256:
        raise ValueError("RA-06 source lock does not pin the frozen final theorem")
    root = project / MODULE_ROOT
    if not root.is_dir() or root.is_symlink():
        raise ValueError("RA-06 copied NLA source directory is absent or a symlink")
    actual_entries = list(root.rglob("*"))
    if any(path.is_symlink() for path in actual_entries):
        raise ValueError("RA-06 copied source contains a symlink")
    actual = {path.relative_to(project).as_posix() for path in actual_entries if path.is_file()}
    if actual != set(expected):
        raise ValueError("RA-06 copied module set differs from frozen import closure")
    for name, digest in expected.items():
        path = project / name
        if not path.is_file() or path.is_symlink() or sha256(path) != digest:
            raise ValueError(f"RA-06 frozen source changed: {name}")
