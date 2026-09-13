"""Verify the distributed snapshot without third-party dependencies.

Run before regenerating logs or rebuilding the PDF. Reproduction intentionally
changes some recorded-output hashes and does not alter the original prior ZIP.
"""
from __future__ import annotations
import argparse
import hashlib
from pathlib import Path
import sys


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def verify(root: Path) -> int:
    root = root.resolve()
    manifest = root / 'MANIFEST.sha256'
    if not manifest.is_file():
        print(f'Missing manifest: {manifest}', file=sys.stderr)
        return 2
    failures: list[str] = []
    count = 0
    for number, line in enumerate(manifest.read_text(encoding='utf-8').splitlines(), 1):
        if not line.strip() or line.startswith('#'):
            continue
        try:
            expected, relative = line.split('  ', 1)
            if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
                raise ValueError('invalid SHA-256 digest')
            target = root / relative
            resolved = target.resolve()
            if resolved == root or root not in resolved.parents:
                raise ValueError('path escapes the package directory')
            if target.is_symlink():
                raise ValueError('symlinks are not allowed in the snapshot')
            if not target.is_file():
                failures.append(f'MISSING {relative}')
            elif digest(target) != expected:
                failures.append(f'CHANGED {relative}')
            count += 1
        except (ValueError, OSError) as exc:
            failures.append(f'Invalid manifest line {number}: {exc}')
    if failures:
        print('\n'.join(failures), file=sys.stderr)
        print(f'{len(failures)} integrity issue(s) among {count} listed files.', file=sys.stderr)
        return 1
    print(f'PASS: all {count} listed files match their SHA-256 digests.')
    return 0


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    raise SystemExit(verify(args.root))
