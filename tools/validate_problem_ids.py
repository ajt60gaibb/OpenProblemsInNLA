#!/usr/bin/env python3
"""Check permanent problem IDs against their registry and a published git tree."""

import argparse
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = "problem_ids.json"
CATEGORIES = [
    "linear-systems-and-elimination", "eigenvalues-and-inverse-problems",
    "matrix-functions-and-stability", "randomized-and-low-rank-approximation",
    "tensor-computations", "nonnegative-and-positive-factorizations",
    "matrix-inequalities-and-norms", "frames-and-matrix-designs",
    "matrix-discrepancy-and-optimization", "arithmetic-and-complexity",
    "intervals-and-absolute-value-equations",
]
ID = re.compile(r"([A-Z]{2})-([0-9]{2,})\Z")


def id_parts(identifier):
    match = ID.fullmatch(identifier) if isinstance(identifier, str) else None
    if not match or int(match[2]) < 1 or match[2] != f"{int(match[2]):02d}":
        raise ValueError(f"Invalid problem ID: {identifier!r}")
    return match[1], int(match[2])


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate registry ID: {key}")
        result[key] = value
    return result


def read_registry(text):
    registry = json.loads(text, object_pairs_hook=unique_object)
    if not isinstance(registry, dict):
        raise ValueError("The problem ID registry must be a JSON object")
    for identifier, path in registry.items():
        id_parts(identifier)
        if not isinstance(path, str):
            raise ValueError(f"{identifier}: registry path must be a string")
        parts = PurePosixPath(path).parts
        if (len(parts) != 3 or parts[0] not in CATEGORIES
                or parts[1:] != (identifier, "README.md")
                or path != "/".join(parts)):
            raise ValueError(f"{identifier}: invalid canonical path {path!r}")
    return registry


def discover(paths, read_text):
    """Discover canonical entry headings; archives and category indexes are excluded."""
    entries = {}
    for path in sorted(paths):
        parts = PurePosixPath(path).parts
        if len(parts) != 3 or parts[0] not in CATEGORIES or parts[2] != "README.md":
            continue
        lines = read_text(path).splitlines()
        heading = lines[0] if lines else ""
        match = re.fullmatch(r"# ([A-Z]{2}-[0-9]{2,}) — (\S.*)", heading)
        if not match:
            raise ValueError(f"{path}: expected '# ID — Problem title' on the first line")
        identifier = match[1]
        id_parts(identifier)
        if identifier in entries:
            raise ValueError(f"Duplicate problem ID {identifier}: {entries[identifier]} and {path}")
        if parts[1] != identifier:
            raise ValueError(f"{path}: directory and heading ID {identifier} differ")
        entries[identifier] = path
    return entries


def same_entries(registry, entries, label):
    for identifier, path in registry.items():
        if identifier not in entries:
            raise ValueError(f"{label}: missing registered entry {identifier} at {path}; retain its page")
        if entries[identifier] != path:
            raise ValueError(f"{label}: {identifier} moved from its permanent path {path} to {entries[identifier]}")
    for identifier, path in entries.items():
        if identifier not in registry:
            raise ValueError(f"{label}: unregistered entry {identifier} at {path}; add it to {REGISTRY}")


def git(root, *args):
    result = subprocess.run(["git", "-C", str(root), *args], capture_output=True, check=False)
    if result.returncode:
        raise ValueError(result.stderr.decode("utf-8", errors="replace").strip())
    return result.stdout


def base_registry(root, base_ref):
    commit = git(root, "rev-parse", "--verify", "--end-of-options", f"{base_ref}^{{commit}}").decode().strip()
    paths = git(root, "ls-tree", "-r", "-z", "--name-only", commit).decode().split("\0")

    def read_text(path):
        return git(root, "show", f"{commit}:{path}").decode("utf-8")

    entries = discover(paths, read_text)
    if REGISTRY not in paths:
        return entries  # Protect already-published IDs when introducing the registry.
    registry = read_registry(read_text(REGISTRY))
    same_entries(registry, entries, f"Base {base_ref}")
    return registry


def default_base_ref(root):
    # Source archives have no history; CI always supplies the historical commit.
    return "HEAD" if (root / ".git").exists() else None


def validate(root=ROOT, base_ref=None):
    root = Path(root)
    if (root / REGISTRY).is_symlink():
        raise ValueError("The problem ID registry must not be a symlink")
    registry = read_registry((root / REGISTRY).read_text(encoding="utf-8"))
    paths = []
    for category in CATEGORIES:
        folder = root / category
        for path in folder.glob("*/README.md"):
            if any(p.is_symlink() for p in (folder, path.parent, path)):
                raise ValueError(f"Canonical entry must not be a symlink: {path.relative_to(root)}")
            paths.append(path.relative_to(root).as_posix())
        for entry in folder.iterdir() if folder.is_dir() else []:
            if entry.is_dir() and ID.fullmatch(entry.name) and not (entry / "README.md").is_file():
                raise ValueError(f"Missing canonical README: {entry.relative_to(root)}")
    entries = discover(paths, lambda path: (root / path).read_text(encoding="utf-8"))
    same_entries(registry, entries, "Current tree")
    if base_ref is not None:
        published = base_registry(root, base_ref)
        maximum = {}
        for identifier, path in published.items():
            if registry.get(identifier) != path:
                raise ValueError(f"Published ID {identifier} must remain registered at {path}")
            prefix, number = id_parts(identifier)
            maximum[prefix] = max(maximum.get(prefix, 0), number)
        for identifier in registry.keys() - published.keys():
            prefix, number = id_parts(identifier)
            if number <= maximum.get(prefix, 0):
                raise ValueError(f"New ID {identifier} must exceed published {prefix}-{maximum[prefix]:02d}; never fill gaps or recycle IDs")
    return len(entries)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-ref", default=default_base_ref(ROOT),
                        help="Historical git commit/ref (default: HEAD in a git checkout)")
    args = parser.parse_args()
    try:
        count = validate(ROOT, args.base_ref)
    except (OSError, ValueError) as error:
        parser.exit(1, f"Problem ID validation failed: {error}\n")
    scope = f"against {args.base_ref}" if args.base_ref else "(current tree only; source archive has no git history)"
    print(f"Validated {count} permanent problem IDs {scope}")


if __name__ == "__main__":
    main()
