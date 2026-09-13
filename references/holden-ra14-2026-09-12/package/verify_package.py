"""Verify the delivered package's SHA-256 manifest (not mathematical validity)."""
from __future__ import annotations

import hashlib
from pathlib import Path
import sys


def main() -> int:
    root = Path(__file__).resolve().parent
    manifest = root / "SHA256SUMS"
    if not manifest.is_file():
        print("Missing SHA256SUMS", file=sys.stderr)
        return 1
    count = 0
    errors: list[str] = []
    for number, line in enumerate(manifest.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        try:
            expected, relative = line.split("  ", 1)
            if len(expected) != 64 or any(c not in "0123456789abcdef" for c in expected):
                raise ValueError("invalid digest")
            path = (root / relative).resolve()
            if not path.is_relative_to(root):
                raise ValueError("path is outside the package")
            if not path.is_file():
                raise ValueError("file does not exist")
            actual = hashlib.sha256(path.read_bytes()).hexdigest()
            if actual != expected:
                errors.append(f"Checksum mismatch: {relative}")
            count += 1
        except (ValueError, OSError) as exc:
            errors.append(f"Manifest line {number}: {exc}")
    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1
    print(f"Verified {count} file checksums. This checks integrity, not proof correctness.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
