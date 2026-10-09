#!/usr/bin/env python3
"""Review-bound statement elaboration, never verification of a problem's truth."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PACKAGE = Path("lean-statements")
ID = re.compile(r"[A-Z]{2}-[0-9]{2,}\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
IMPORT = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$", re.MULTILINE)
PINS = [PACKAGE / f for f in ("lakefile.toml", "lake-manifest.json", "lean-toolchain")]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def unique(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(path: Path):
    return json.loads(path.read_text(), object_pairs_hook=unique)


def contained(root: Path, relative: str) -> Path:
    path = Path(relative)
    if path.is_absolute() or path.as_posix() != relative or ".." in path.parts:
        raise ValueError(f"invalid relative path: {relative}")
    full = root / path
    if any(p.is_symlink() for p in (full, *full.parents)):
        raise ValueError(f"symbolic links are not retained statement inputs: {relative}")
    if not full.is_file():
        raise ValueError(f"missing input: {relative}")
    return full


def check_hash(root: Path, relative: str, expected: str) -> None:
    if not isinstance(expected, str) or not SHA256.fullmatch(expected):
        raise ValueError(f"invalid hash: {relative}")
    if digest(contained(root, relative)) != expected:
        raise ValueError(f"changed reviewed input: {relative}")


def source_path(problem_id: str) -> Path:
    if not ID.fullmatch(problem_id):
        raise ValueError(f"invalid permanent ID: {problem_id}")
    return PACKAGE / "NLA/Statements" / (problem_id.replace("-", "") + ".lean")


def frozen_path(problem_id: str) -> Path:
    return PACKAGE / "Reviewed" / (problem_id.replace("-", "") + ".lean")


def local_imports(root: Path, relative: Path, found=None) -> set[Path]:
    """Bind every repository-local imported module, not just the target file.

    Package modules must use one plain import per line. External imports are
    bound by the immutable dependency manifest and reviewed dependency meaning.
    """
    found = set() if found is None else found
    if relative in found:
        return found
    found.add(relative)
    content = contained(root, relative.as_posix()).read_text()
    imports = IMPORT.findall(content)
    for line in content.splitlines():
        if re.match(r"^\s*(?:(?:public|private)\s+)?import\b", line) and not IMPORT.fullmatch(line):
            raise ValueError(f"use one plain import per line: {relative}")
    for module in imports:
        path = PACKAGE / (module.replace(".", "/") + ".lean")
        if (root / path).exists():
            local_imports(root, path, found)
    return found


def review_inputs(root: Path, metadata: dict, phase: str) -> set[str]:
    inputs = {metadata["canonical_readme"], metadata["specification"],
              f"docs/lean/statements/{metadata['id']}/ORIGINAL.md"}
    if phase == "lean-boundary":
        inputs |= {p.as_posix() for p in PINS}
        inputs |= {p.as_posix() for p in local_imports(root, source_path(metadata["id"]))}
        inputs |= {p.as_posix() for p in local_imports(root, frozen_path(metadata["id"]))}
    return inputs


def validate_metadata(root: Path, path: Path, *, require_reviews: bool = True) -> dict:
    contained(root, path.relative_to(root).as_posix())
    data = read_json(path)
    problem_id = data["id"]
    compact = problem_id.replace("-", "")
    source = source_path(problem_id)
    registry = read_json(root / "problem_ids.json")
    expected_metadata = root / "docs/lean/statements" / problem_id / "statement.json"
    if path != expected_metadata:
        raise ValueError(f"metadata is outside its permanent-ID directory: {path}")
    if data.get("schema_version") != 1 or data.get("scope") != "statement-only":
        raise ValueError("metadata must explicitly declare schema 1 and statement-only scope")
    if data.get("canonical_readme") != registry.get(problem_id):
        raise ValueError(f"canonical registry correspondence failed: {problem_id}")
    if data.get("specification") != f"docs/lean/statements/{problem_id}/NUMERICAL_TARGETS.md":
        raise ValueError("specification must be retained beside its metadata")
    original = contained(root, f"docs/lean/statements/{problem_id}/ORIGINAL.md")
    canonical = contained(root, data["canonical_readme"])
    if original.read_bytes() != canonical.read_bytes():
        raise ValueError("ORIGINAL.md must preserve the complete canonical README byte for byte")
    if data.get("module") != f"NLA.Statements.{compact}" or data.get("declaration") != f"NLA.Statements.{compact}.Target":
        raise ValueError("module/declaration must retain the permanent ID")
    for relative, key in [(data["canonical_readme"], "source_sha256"),
                          (data["specification"], "specification_sha256"),
                          (source.as_posix(), "lean_sha256"),
                          (frozen_path(problem_id).as_posix(), "frozen_sha256")]:
        check_hash(root, relative, data[key])
    authors = data.get("authors", [])
    if not isinstance(authors, list) or not authors or any(not isinstance(a, str) or not a.strip() for a in authors):
        raise ValueError("name the nonempty list of statement authors")
    for phase in ("specification", "lean-boundary"):
        reviewers = set()
        for review in data.get("reviews", []):
            if review.get("phase") != phase:
                continue
            reviewer = review.get("reviewer", "")
            if not reviewer or reviewer in authors or reviewer in reviewers:
                raise ValueError("reviewers must be named, distinct and independent of authors")
            if review.get("is_ai") is not True or review.get("verdict") != "approve":
                raise ValueError("this agent workflow requires explicitly disclosed AI approval reviews")
            check_hash(root, review["report_path"], review["report_sha256"])
            bindings = review.get("input_sha256", {})
            if not review_inputs(root, data, phase) <= bindings.keys():
                raise ValueError(f"{phase} review omits source, specification, or Lean import closure")
            for relative, sha in bindings.items():
                check_hash(root, relative, sha)
            reviewers.add(reviewer)
        if require_reviews and len(reviewers) < 2:
            raise ValueError(f"{problem_id}: two independent {phase} approvals required")
    return data


def discover(root: Path) -> list[Path]:
    return sorted((root / "docs/lean/statements").glob("*/statement.json"))


def freeze(root: Path, problem_id: str) -> None:
    source = contained(root, source_path(problem_id).as_posix())
    compact = problem_id.replace("-", "")
    old = f"NLA.Statements.{compact}"
    new = f"NLA.ReviewedStatements.{compact}"
    content = source.read_text()
    if content.count(f"namespace {old}\n") != 1 or content.count(f"end {old}") != 1:
        raise ValueError("freeze requires exactly one full permanent-ID namespace and matching end")
    destination = root / frozen_path(problem_id)
    if destination.exists():
        raise ValueError("frozen boundary already exists; deliberate revisions require new reviews")
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text("/- Frozen statement boundary. Changes reopen independent review. -/\n" +
                           content.replace(old, new))
    print(destination.relative_to(root))


def computation_controls(root: Path) -> list[str]:
    """Discover only direct computation control modules, in stable order."""
    directory = root / PACKAGE / "NLA/Computation"
    modules = []
    for path in sorted(directory.glob("*Controls.lean")):
        if path.is_file():
            relative = path.relative_to(root)
            contained(root, relative.as_posix())
            modules.append("NLA.Computation." + path.stem)
    return modules


def generated_checks(root: Path, entries: list[dict]) -> str:
    imports = ["import NLA", "import StatementControls",
               "import NLA.Statements.Infrastructure", "import LeanCert.Tactic.Verification"]
    imports.extend(f"import {module}" for module in computation_controls(root))
    body = ["set_option leancert.trust \"kernel\"", "set_option autoImplicit false"]
    for data in entries:
        compact = data["id"].replace("-", "")
        imports.extend([f"import {data['module']}", f"import Reviewed.{compact}"])
        target = data["declaration"]
        reviewed = f"NLA.ReviewedStatements.{compact}.Target"
        body.extend([f"#assert_statement {target}", f"#assert_statement {reviewed}",
                     f"#assert_trust kernel {target}", f"#print axioms {target}",
                     f"example : {target} = {reviewed} := by rfl"])
    return "\n".join(imports + [""] + body) + "\n"


def identity_files(entries: list[dict]) -> dict[str, str]:
    imports = ["import NLA.Statements.KernelSmoke"]
    challenge = []
    solution = []
    names = ["NLA.Statements.ComparatorControl.log_two_upper"]
    challenge.append("theorem log_two_upper : Real.log 2 < (7 / 10 : ℝ) := by sorry")
    solution.extend(["theorem log_two_upper : Real.log 2 < (7 / 10 : ℝ) :=",
                     "  NLA.Statements.KernelSmoke.log_two_upper"])
    for data in entries:
        compact = data["id"].replace("-", "")
        imports.extend([f"import {data['module']}", f"import Reviewed.{compact}"])
        name = "identity_" + compact
        signature = f"theorem {name} : {data['declaration']} = NLA.ReviewedStatements.{compact}.Target := by "
        challenge.append(signature + "sorry")
        solution.append(signature + "rfl")
        names.append("NLA.Statements.ComparatorControl." + name)
    solution.extend(f"#assert_trust kernel {name}" for name in names)
    solution.extend(f"#print axioms {name}" for name in names)
    prefix = "\n".join(imports) + "\n\n/- Generated identity certificates only; no catalog proposition is asserted. -/\nnamespace NLA.Statements.ComparatorControl\n"
    suffix = "\nend NLA.Statements.ComparatorControl\n"
    config = {"challenge_module": "IdentityChallenge", "solution_module": "IdentitySolution",
              "theorem_names": names, "definition_names": [],
              "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"]}
    return {"IdentityChallenge.lean": prefix + "\n".join(challenge) + suffix,
            "IdentitySolution.lean": prefix + "\n".join(solution) + suffix,
            "comparator.json": json.dumps(config, indent=2) + "\n"}


def require_retained(root: Path, base_ref: str) -> None:
    tracked = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", "-z", base_ref,
                                      "--", "docs/lean/statements", "lean-statements"], cwd=root, text=True).split("\0")
    for relative in tracked:
        if relative.endswith("/statement.json") or re.fullmatch(r"lean-statements/(?:NLA/Statements|Reviewed)/[A-Z]{2}[0-9]{2,}\.lean", relative):
            contained(root, relative)


def validate_package(root: Path) -> None:
    toolchain = contained(root, (PACKAGE / "lean-toolchain").as_posix()).read_text().strip()
    if toolchain != "leanprover/lean4:v4.33.1":
        raise ValueError("the reviewed statement toolchain must remain Lean 4.33.1")
    manifest = read_json(contained(root, (PACKAGE / "lake-manifest.json").as_posix()))
    if manifest.get("packagesDir") != ".lake/packages":
        raise ValueError("dependencies must use the contained .lake/packages directory")
    packages = manifest.get("packages", [])
    if len({p.get("name") for p in packages}) != len(packages):
        raise ValueError("duplicate dependency name")
    for package in packages:
        if package.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", package.get("rev", "")) or not re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", package.get("url", "")):
            raise ValueError("every dependency needs an exact credential-free HTTPS GitHub git pin")
    pins = {p["name"]: p["rev"] for p in packages}
    if pins.get("leancert") != "621a43d7cf21f87872392a01e874f2f1dbddc926" or pins.get("mathlib") != "0df444a360eaa60ab8c11dca51a86af692955474":
        raise ValueError("LeanCert and Mathlib must match the shared reviewed pins")


def validate_all(root: Path, *, require_reviews: bool = True, base_ref: str | None = None) -> list[dict]:
    validate_package(root)
    if base_ref:
        require_retained(root, base_ref)
    entries = [validate_metadata(root, p, require_reviews=require_reviews) for p in discover(root)]
    expected = {source_path(e["id"]) for e in entries}
    actual = set((root / PACKAGE / "NLA/Statements").glob("[A-Z][A-Z][0-9]*.lean"))
    if {p.relative_to(root) for p in actual} != expected:
        raise ValueError("every permanent-ID module must have reviewed metadata; metadata may not omit modules")
    snapshots = {p.relative_to(root) for p in (root / PACKAGE / "Reviewed").glob("*.lean")}
    if snapshots != {frozen_path(e["id"]) for e in entries}:
        raise ValueError("every frozen boundary must correspond to a declared statement")
    for name, expected_content in identity_files(entries).items():
        if (root / PACKAGE / name).read_text() != expected_content:
            raise ValueError(f"identity certificate coverage is stale: {name}; run refresh-identities")
    return entries


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--base-ref", help="published base for retained statement/module checks")
    parser.add_argument("--draft", action="store_true", help="development only; omit approval-count gate")
    commands = parser.add_subparsers(dest="action", required=True)
    commands.add_parser("validate")
    commands.add_parser("refresh-identities")
    frozen = commands.add_parser("freeze")
    frozen.add_argument("id")
    check = commands.add_parser("elaborate")
    check.add_argument("--output", type=Path, required=True, help="receipt directory outside source")
    args = parser.parse_args()
    root = args.root.resolve()
    if args.action == "freeze":
        freeze(root, args.id)
        return
    if args.action == "refresh-identities":
        entries = [read_json(p) for p in discover(root)]
        for name, content in identity_files(entries).items():
            (root / PACKAGE / name).write_text(content)
        return
    entries = validate_all(root, require_reviews=not args.draft, base_ref=args.base_ref)
    if args.action == "validate":
        print(f"PASS: {len(entries)} statement metadata records; no mathematical proof claim")
        return
    output = args.output.resolve()
    if output.is_relative_to(root / PACKAGE):
        parser.error("elaboration evidence must be outside the Lean source package")
    output.mkdir(parents=True, exist_ok=True)
    inputs = {p.relative_to(root).as_posix(): digest(p) for p in (root / PACKAGE).rglob("*.lean") if ".lake" not in p.parts}
    inputs.update({p.as_posix(): digest(root / p) for p in PINS})
    modules = ["NLA", "StatementControls", "IdentitySolution"]
    modules.extend(computation_controls(root))
    modules.extend(e["module"] for e in entries)
    modules.extend("Reviewed." + e["id"].replace("-", "") for e in entries)
    build = subprocess.run(["lake", "build", *modules], cwd=root / PACKAGE, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (output / "build.log").write_text(build.stdout)
    if build.returncode:
        raise SystemExit(build.returncode)
    checkfile = output / "CheckStatements.lean"
    checkfile.write_text(generated_checks(root, entries))
    result = subprocess.run(["lake", "env", "lean", str(checkfile)], cwd=root / PACKAGE, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (output / "statements.log").write_text(result.stdout)
    for relative, sha in inputs.items():
        check_hash(root, relative, sha)
    validate_all(root, require_reviews=not args.draft, base_ref=args.base_ref)
    receipt = {"scope": "statement elaboration and frozen-boundary identity only; no problem proved",
               "authoritative_linux_comparator": False, "draft": args.draft,
               "input_sha256": inputs, "ids": [e["id"] for e in entries],
               "elaboration_passed": result.returncode == 0,
               "logs": {p.name: digest(p) for p in [output / "build.log", output / "statements.log"]}}
    (output / "result.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(result.stdout)
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
