#!/usr/bin/env python3
"""Discover registered Lean projects and select only affected projects for CI."""
from __future__ import annotations
import argparse
import json
from pathlib import Path, PurePosixPath
import subprocess


def discover(root: Path) -> list[dict[str, str]]:
    registry = json.loads((root / "problem_ids.json").read_text())
    result = []
    for problem_id, canonical in sorted(registry.items()):
        relative = PurePosixPath(canonical).parent / "lean"
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError(f"Invalid registry path: {canonical}")
        project = root / relative
        if any((project / name).exists() for name in
               ("lean-toolchain", "lakefile.toml", "lakefile.lean", "formalization.yaml")):
            result.append({"id": problem_id, "project": relative.as_posix()})
    return result


def select(projects: list[dict[str, str]], changed: list[str]) -> list[dict[str, str]]:
    shared = ("tools/lean/", "docs/lean/schema/", ".github/workflows/lean-verification.yml")
    if any(path == "problem_ids.json" or any(path.startswith(p) for p in shared)
           for path in changed):
        return projects
    return [p for p in projects if any(
        path.startswith(str(PurePosixPath(p["project"]).parent) + "/")
        for path in changed)]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[2])
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--all", action="store_true")
    group.add_argument("--base-ref")
    parser.add_argument("--github-output", type=Path)
    args = parser.parse_args()
    projects = discover(args.root)
    if not args.all:
        changed = subprocess.check_output(
            ["git", "diff", "--name-only", "--no-renames", args.base_ref, "HEAD", "--"],
            cwd=args.root, text=True).splitlines()
        projects = select(projects, changed)
    encoded = json.dumps({"include": projects}, separators=(",", ":"))
    print(encoded)
    if args.github_output:
        with args.github_output.open("a") as stream:
            stream.write(f"matrix={encoded}\ncount={len(projects)}\n")


if __name__ == "__main__":
    main()
