#!/usr/bin/env python3
"""Lock or verify one stable computer-assisted-proof artifact."""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HASH_RE = re.compile(r"(?m)^([0-9a-f]{64})  (.+)$")


def fail(message: str) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(2)


def artifact(raw: str) -> tuple[Path, str]:
    candidate = Path(raw)
    unresolved = candidate if candidate.is_absolute() else ROOT / candidate
    if unresolved.is_symlink():
        fail("give the proof artifact itself, not a symlink")
    path = unresolved.resolve()
    try:
        relative = path.relative_to(ROOT).as_posix()
    except ValueError:
        fail("the artifact must be inside this repository")
    if not path.is_file():
        fail("give one existing regular file, not a directory, glob, or collection")
    if relative.startswith((".git/", ".codex/")) or relative.endswith(".proof.sha256"):
        fail("repository metadata, policy files, and hash sidecars are not proof artifacts")
    return path, relative


def sidecar(path: Path) -> Path:
    return path.with_name(path.name + ".proof.sha256")


def sha256(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def recorded_hash(lockfile: Path, expected_name: str) -> str:
    match = HASH_RE.search(lockfile.read_text(encoding="utf-8"))
    if match is None or match.group(2) != expected_name:
        fail(f"malformed individual lock file: {lockfile.relative_to(ROOT)}")
    return match.group(1)


def lock(path: Path, relative: str, reason: str) -> None:
    reason = " ".join(reason.split())
    if not reason:
        fail("state the mathematical role of this artifact")
    lockfile = sidecar(path)
    current = sha256(path)
    if lockfile.exists():
        if recorded_hash(lockfile, path.name) == current:
            print(f"Already locked and unchanged: {relative}\nSHA-256: {current}")
            return
        fail("this locked artifact changed; create a versioned replacement instead of replacing its hash")
    lockfile.write_text(
        "# INDIVIDUAL LOCKED COMPUTER-ASSISTED-PROOF ARTIFACT\n"
        f"# Mathematical role: {reason}\n"
        f"{current}  {path.name}\n",
        encoding="utf-8",
    )
    print(f"Locked one proof artifact: {relative}\nSHA-256: {current}")


def verify(path: Path, relative: str) -> None:
    lockfile = sidecar(path)
    if not lockfile.is_file():
        fail("this exact file has no adjacent .proof.sha256 lock")
    expected = recorded_hash(lockfile, path.name)
    current = sha256(path)
    if current != expected:
        fail(f"locked proof artifact changed: {relative}")
    print(f"Verified unchanged: {relative}\nSHA-256: {current}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Hash exactly one stable proof-bearing file.")
    sub = parser.add_subparsers(dest="action", required=True)
    make = sub.add_parser("lock")
    make.add_argument("path")
    make.add_argument("--reason", required=True)
    check = sub.add_parser("verify")
    check.add_argument("path")
    args = parser.parse_args()
    path, relative = artifact(args.path)
    lock(path, relative, args.reason) if args.action == "lock" else verify(path, relative)


if __name__ == "__main__":
    main()
