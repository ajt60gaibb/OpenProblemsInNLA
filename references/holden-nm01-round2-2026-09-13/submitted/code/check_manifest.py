#!/usr/bin/env python3
"""Verify every delivered file against MANIFEST.sha256 (standard library only).

The manifest itself is excluded from its own checksums. Additional files,
including Python caches and later user-generated reports, are not errors.
"""
from __future__ import annotations
import argparse
import hashlib
from pathlib import Path


def verify(root: Path) -> int:
    root = root.resolve()
    manifest = root / 'MANIFEST.sha256'
    if not manifest.is_file():
        raise ValueError(f'Missing manifest: {manifest}')
    count = 0
    seen: set[str] = set()
    for lineno, line in enumerate(manifest.read_text(encoding='utf-8').splitlines(), 1):
        if not line.strip():
            continue
        try:
            expected, relative = line.split('  ', 1)
        except ValueError as exc:
            raise ValueError(f'Malformed manifest line {lineno}') from exc
        if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
            raise ValueError(f'Invalid SHA-256 on line {lineno}')
        target = (root / relative).resolve()
        if not target.is_relative_to(root) or relative in seen:
            raise ValueError(f'Unsafe or duplicate manifest entry on line {lineno}')
        seen.add(relative)
        if not target.is_file():
            raise ValueError(f'Missing file: {relative}')
        actual = hashlib.sha256(target.read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f'SHA-256 mismatch: {relative}')
        count += 1
    if count == 0:
        raise ValueError('Empty manifest')
    return count


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    try:
        count = verify(args.root)
    except (OSError, ValueError) as exc:
        parser.exit(1, f'Manifest verification failed: {exc}\n')
    print(f'SHA-256 verified for all {count} listed files.')


if __name__ == '__main__':
    main()
