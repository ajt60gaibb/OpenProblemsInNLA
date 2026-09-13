#!/usr/bin/env python3
"""Verify the packaged file manifest; this does not check mathematical claims."""
from __future__ import annotations
import hashlib
import sys
from pathlib import Path, PurePosixPath


def main() -> int:
    root = Path(__file__).resolve().parent
    manifest = root / 'SHA256SUMS.txt'
    failures = []
    count = 0
    try:
        lines = manifest.read_text(encoding='utf-8').splitlines()
    except OSError as exc:
        print(f'Cannot read manifest: {exc}', file=sys.stderr)
        return 1
    seen = set()
    for line in lines:
        if not line.strip():
            continue
        try:
            expected, name = line.split('  ', 1)
            rel = PurePosixPath(name)
            if (len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected)
                    or rel.is_absolute() or '..' in rel.parts or name in seen):
                raise ValueError('invalid or duplicate manifest entry')
            seen.add(name)
            path = root.joinpath(*rel.parts).resolve()
            if not path.is_relative_to(root):
                raise ValueError('path escapes package root')
            if not path.is_file():
                failures.append(f'MISSING: {name}')
                continue
            with path.open('rb') as handle:
                actual = hashlib.file_digest(handle, 'sha256').hexdigest()
            if actual != expected:
                failures.append(f'CHANGED: {name}')
            count += 1
        except (ValueError, OSError) as exc:
            failures.append(f'INVALID: {line!r}: {exc}')
    if failures:
        print('\n'.join(failures), file=sys.stderr)
        return 1
    if count == 0:
        print('Manifest is empty.', file=sys.stderr)
        return 1
    print(f'Integrity verified: {count} files. This is not mathematical verification.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
