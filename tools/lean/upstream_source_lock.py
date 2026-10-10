#!/usr/bin/env python3
"""Check the immutable MF-23 direct-proof source closure before verification."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re


PINNED_COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
PINNED_TREE = "5374ca34f6707460b2d2a3eb98b1ae7af6ea25ff"
PINNED_LOCK_SHA256 = "debce830554cb3f83e1fd7066324655bada786f1c5f7291a8aa11794ab60d511"
PINNED_LICENSE_SHA256 = "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4"
MODULE_DIR = Path("OAI/Analysis/DirectCrouzeix")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate MF-23 source-lock key: {key}")
        result[key] = value
    return result


def validate_mf23_source_lock(project: Path) -> None:
    """Reject changed, missing, or extra copied upstream Lean modules."""
    lockfile = project / "upstream-source-lock.json"
    if not lockfile.is_file() or lockfile.is_symlink() or sha256(lockfile) != PINNED_LOCK_SHA256:
        raise ValueError("MF-23 upstream source lock is absent or changed")
    lock = json.loads(lockfile.read_text(), object_pairs_hook=_unique_pairs)
    if (lock.get("schema_version") != 1
            or lock.get("upstream_repository") != "https://github.com/openai/math"
            or lock.get("upstream_commit") != PINNED_COMMIT
            or lock.get("upstream_direct_proof_tree") != PINNED_TREE
            or lock.get("entry_point") != str(MODULE_DIR / "CompleteBound.lean")
            or lock.get("excluded_unneeded_upstream_module") != str(MODULE_DIR / "Main.lean")):
        raise ValueError("MF-23 source lock has incorrect pinned provenance")
    entries = lock.get("files")
    if not isinstance(entries, list) or len(entries) != 41:
        raise ValueError("MF-23 source lock must contain the 41-module import closure")
    expected: dict[str, str] = {}
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != {"path", "sha256"}:
            raise ValueError("malformed MF-23 source-lock entry")
        name, digest = entry["path"], entry["sha256"]
        if (not isinstance(name, str) or not name.startswith(str(MODULE_DIR) + "/")
                or not re.fullmatch(r"[A-Za-z][A-Za-z0-9]*\.lean", name.rsplit("/", 1)[-1])
                or not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest)
                or name in expected):
            raise ValueError("invalid or duplicate MF-23 source-lock path/hash")
        expected[name] = digest
    if str(MODULE_DIR / "CompleteBound.lean") not in expected:
        raise ValueError("MF-23 source lock omits its theorem entry point")
    folder = project / MODULE_DIR
    if not folder.is_dir() or folder.is_symlink():
        raise ValueError("MF-23 direct-proof directory is absent or a symlink")
    actual = {p.relative_to(project).as_posix() for p in folder.iterdir()}
    if actual != set(expected):
        raise ValueError("MF-23 direct-proof module set differs from pinned closure")
    for name, digest in expected.items():
        source = project / name
        if not source.is_file() or source.is_symlink() or sha256(source) != digest:
            raise ValueError(f"MF-23 pinned source changed: {name}")
    license_file = project / "UPSTREAM-LICENSE.txt"
    if (not license_file.is_file() or license_file.is_symlink()
            or sha256(license_file) != PINNED_LICENSE_SHA256):
        raise ValueError("MF-23 upstream Apache-2.0 license text changed")
