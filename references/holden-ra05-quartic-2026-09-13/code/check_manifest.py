"""Verify the packaged files listed in SHA256SUMS (standard library only)."""
from __future__ import annotations
import hashlib
from pathlib import Path
import sys


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    manifest = root / 'SHA256SUMS'
    if not manifest.is_file():
        print('Missing SHA256SUMS', file=sys.stderr)
        return 1
    checked = 0
    for line in manifest.read_text().splitlines():
        if not line.strip():
            continue
        expected, name = line.split('  ', 1)
        path = (root / name).resolve()
        if not path.is_relative_to(root) or not path.is_file():
            print(f'Missing or invalid path: {name}', file=sys.stderr)
            return 1
        with path.open('rb') as stream:
            actual = hashlib.file_digest(stream, 'sha256').hexdigest()
        if actual != expected:
            print(f'Hash mismatch: {name}', file=sys.stderr)
            return 1
        checked += 1
    print(f'PASS: {checked} recorded SHA-256 hashes match.')
    print('The manifest is not an external digital signature or a mathematical proof.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
