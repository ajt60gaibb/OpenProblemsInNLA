#!/usr/bin/env python3
"""Discover registered Lean projects and select only affected projects for CI."""
from __future__ import annotations
import argparse
import json
from pathlib import Path, PurePosixPath
import subprocess


def registered_projects(registry: dict[str, str]) -> list[dict[str, str]]:
    result = []
    for problem_id, canonical in sorted(registry.items()):
        relative = PurePosixPath(canonical).parent / "lean"
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError(f"Invalid registry path: {canonical}")
        result.append({"id": problem_id, "project": relative.as_posix()})
    return result


def discover(root: Path) -> list[dict[str, str]]:
    registry = json.loads((root / "problem_ids.json").read_text())
    result = []
    for entry in registered_projects(registry):
        project = root / entry["project"]
        # Even a source-only draft must be selected, so missing metadata or build
        # inputs fail validation instead of silently skipping verification.
        if project.exists() or project.is_symlink():
            if project.is_symlink() or not project.is_dir():
                raise ValueError(f"Lean project must be an ordinary directory: {entry['project']}")
            result.append(entry)
    return result


def discover_at_ref(root: Path, ref: str) -> list[dict[str, str]]:
    registry = json.loads(subprocess.check_output(
        ["git", "show", f"{ref}:problem_ids.json"], cwd=root, text=True))
    paths = subprocess.check_output(
        ["git", "ls-tree", "-r", "--name-only", "-z", ref],
        cwd=root, text=True).split("\0")
    return [entry for entry in registered_projects(registry) if any(
        path == entry["project"] or path.startswith(entry["project"] + "/")
        for path in paths)]


def require_retained_projects(projects: list[dict[str, str]],
                              base_projects: list[dict[str, str]]) -> None:
    current_paths = {entry["project"] for entry in projects}
    missing = [entry["project"] for entry in base_projects
               if entry["project"] not in current_paths]
    if missing:
        raise ValueError("Registered Lean projects removed or renamed; verification cannot "
                         "be skipped: " + ", ".join(missing))


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
        require_retained_projects(projects, discover_at_ref(args.root, args.base_ref))
        changed = subprocess.check_output(
            ["git", "diff", "--name-only", "--no-renames", "-z", args.base_ref, "HEAD", "--"],
            cwd=args.root, text=True).split("\0")
        projects = select(projects, changed)
    encoded = json.dumps({"include": projects}, separators=(",", ":"))
    print(encoded)
    if args.github_output:
        with args.github_output.open("a") as stream:
            stream.write(f"matrix={encoded}\ncount={len(projects)}\n")


if __name__ == "__main__":
    main()
