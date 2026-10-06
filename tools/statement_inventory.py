#!/usr/bin/env python3
"""Inventory canonical Lean statements without mistaking archives for coverage.

This is a source/provenance inventory, not a theorem checker or a mathematical
fidelity certificate.  Its base is an explicit published commit, never HEAD.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

from validate_problem_ids import git, id_parts, read_registry

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = "docs/lean/statements/inventory.json"
COVERAGE = "docs/lean/statements/COVERAGE.md"
REPOSITORY = "https://github.com/ajt60gaibb/OpenProblemsInNLA"

# These are documented scope gaps in the published projects, not an automated
# verdict on Lean syntax.  Adding a new reviewed campaign statement can address
# a gap; retaining the old project must not silently erase the historical issue.
SCOPE_GAPS = {
    "IE-21": "The full target is an axiom and the SphericalRowLaw semantic boundary is unimplemented.",
    "IE-22": "The full target is an axiom; complete semantic and proof obligations remain.",
    "IV-02": "ComplexityContract contains unconstrained propositions, without computational semantics.",
    "IV-04": "The complexity target is absent, and raw coordinate sets are required to be intervals instead of defining their hulls.",
    "MD-06": "Graph probability and local-minimum semantics remain parameters of an abstract Semantics structure.",
    "TR-04": "Unfolding rank is an arbitrary function and the operation count is an unconstrained natural-number output.",
}
EXTERNAL_PROJECTS = {
    "IE-01": {
        "repository": "https://github.com/sgstepaniants/Forsythe",
        "revision": "8d1b0c0545a77b40245e84705aa7d273e6c81e62",
        "statement_path": "lean-proof/ProofProject/Definitions.lean",
        "entry_point": "lean-proof/Solution.lean",
    },
    "TR-01": {
        "repository": "https://github.com/yuningyang19/OpenProblemsInNLA_TR-01",
        "revision": "ed21181197ac839eac95f549404f94e7e3aa6e10",
        "statement_path": "lean/Problem56/PaperV7/Certification.lean",
        "entry_point": "lean/Problem56/PaperV7/Certification.lean",
    },
    "MI-15": {
        "repository": "https://github.com/erenup/toeplitz-bw-not-sos",
        "revision": "7126c0841b008dc89a21edfd008bbf1b748d280f",
        "statement_path": "lean/ToeplitzSOS/Defs.lean",
        "entry_point": "lean/ToeplitzSOS/Negative/Resolution.lean",
    },
    "MI-18": {
        "repository": "https://github.com/KitaKen1/bapat-lal-q-permanent-lean",
        "revision": "4200da4fc1a132d69c23fb877795b5b72089544b",
        "statement_path": "lean/Bapat/Main.lean",
        "entry_point": "lean/Bapat/Main.lean",
    },
    "MI-32": {
        "repository": "https://github.com/DiarHaidary/Spectral-norms-of-independent-entries-with-regular-moment-growth",
        "revision": "762bd5ec5050a96f5e6ba3926b6cda4816fcd4b0",
        "statement_path": "Challenge.lean",
        "entry_point": "Solution.lean",
    },
}


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def metadata(text, name, default=None):
    match = re.search(r"(?m)^\*\*" + re.escape(name) + r":\*\*\s*([^\n]+)", text)
    return match[1].strip() if match else default


def local_imports(project):
    """Follow only source imports from the live Challenge/Solution entry points.

    Recursive globbing would count thousands of copied review trees.  An import
    that does not resolve inside this project belongs to a dependency and is not
    traversed.  No `.lake` source is discovered by this function.
    """
    pending = [project / name for name in ("Challenge.lean", "Solution.lean")]
    visited = set()
    while pending:
        source = pending.pop()
        if source in visited or not source.is_file():
            continue
        if not source.resolve().is_relative_to(project.resolve()):
            raise ValueError(f"Project source escapes its root: {source}")
        visited.add(source)
        text = source.read_text(encoding="utf-8")
        for line in text.splitlines():
            if not re.match(r"^\s*(?:public\s+)?import\s", line):
                continue
            modules = re.sub(r"^\s*(?:public\s+)?import\s+", "", line).split("--", 1)[0]
            for module in modules.split():
                module = module.replace("«", "").replace("»", "")
                if re.fullmatch(r"[\w.]+", module):
                    pending.append(project.joinpath(*module.split(".")).with_suffix(".lean"))
    return sorted(visited, key=lambda source: source.as_posix())


def campaign_record(root, identifier, canonical_path, source_hash):
    path = root / "docs/lean/statements" / identifier / "statement.json"
    if not path.is_file():
        return None
    record = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(record, dict):
        raise ValueError(f"{path}: statement metadata must be an object")
    issues = []
    for field, expected in (("id", identifier), ("canonical_readme", canonical_path),
                            ("source_sha256", source_hash), ("scope", "statement-only")):
        if record.get(field) != expected:
            issues.append(f"{field} does not match the canonical source contract")
    module = record.get("module", "")
    # Module names are paths, not shell expressions or arbitrary file references.
    if not isinstance(module, str) or not re.fullmatch(r"NLA\.Statements\.[A-Za-z][A-Za-z0-9_]*", module):
        lean_path = None
        issues.append("module is not a shared NLA.Statements module")
    else:
        lean_path = Path("lean-statements").joinpath(*module.split(".")).with_suffix(".lean")
    exists = lean_path is not None and (root / lean_path).is_file()
    lean_hash = sha256((root / lean_path).read_bytes()) if exists else None
    if not exists:
        issues.append("shared Lean source is missing")
    elif record.get("lean_sha256") != lean_hash:
        issues.append("lean_sha256 does not match the shared source")
    return {
        "metadata_path": path.relative_to(root).as_posix(),
        "module": module,
        "declaration": record.get("declaration"),
        "source_path": lean_path.as_posix() if lean_path else None,
        "source_present": exists,
        "source_sha256": lean_hash,
        "metadata_issues": issues,
        "review_phases_recorded": sorted({r.get("phase") for r in record.get("reviews", [])
                                          if isinstance(r, dict) and isinstance(r.get("phase"), str)}),
        "fidelity_verdict": "not-established-by-inventory",
    }


def complexity_estimate(text):
    """Triage hints only; these are not assessments of proof difficulty."""
    patterns = {
        "computational-model": r"Turing|polynomial.time|query complexity|oracle|decidab|arithmetic operations",
        "probability-and-limits": r"\\Pr|probability|Gaussian|expectation|converg|asymptotic|\\mathbb E",
        "algebraic-geometry": r"Zariski|variet|border.rank|ideal|Cohen|generic|identifiab",
        "operator-analysis": r"Hilbert|semigroup|Schatten|spectral|matrix exponential|functional calculus",
        "finite-algebra-or-combinatorics": r"permanent|Hadamard|rank.one|signing|simple.*graph|addition chain",
    }
    tags = [tag for tag, pattern in patterns.items() if re.search(pattern, text, re.IGNORECASE)]
    demanding = {"computational-model", "probability-and-limits", "algebraic-geometry"}
    return {"level": "high" if demanding.intersection(tags) else "moderate",
            "domains": tags or ["finite-dimensional-linear-algebra"],
            "basis": "keyword triage of canonical README; requires statement-author review"}


def build_inventory(root, base_ref):
    root = Path(root)
    base = git(root, "rev-parse", "--verify", "--end-of-options", f"{base_ref}^{{commit}}").decode().strip()
    registry = read_registry((root / "problem_ids.json").read_text(encoding="utf-8"))
    published = read_registry(git(root, "show", f"{base}:problem_ids.json").decode())
    for identifier, path in published.items():
        if registry.get(identifier) != path:
            raise ValueError(f"{identifier}: published ID or path changed")
    entries = []
    for identifier in sorted(registry, key=id_parts):
        path = registry[identifier]
        data = (root / path).read_bytes()
        text = data.decode("utf-8")
        title_prefix = f"# {identifier} — "
        if not text.startswith(title_prefix):
            raise ValueError(f"{path}: canonical heading does not match its registered ID")
        source_hash = sha256(data)
        base_hash = sha256(git(root, "show", f"{base}:{path}")) if identifier in published else None
        project = (root / path).parent / "lean"
        challenge = project / "Challenge.lean"
        solution = project / "Solution.lean"
        external = EXTERNAL_PROJECTS.get(identifier)
        if external and external["revision"] not in text:
            raise ValueError(f"{identifier}: pinned external source changed; review inventory metadata")
        campaign = campaign_record(root, identifier, path, source_hash)
        if challenge.is_file():
            classification = "local-scope-gap" if identifier in SCOPE_GAPS else "local-statement-source"
        elif external:
            classification = "external-statement-source"
        else:
            classification = "missing-statement"
        if campaign and campaign["source_present"]:
            classification = "shared-statement-source"
        concerns = [SCOPE_GAPS[identifier]] if identifier in SCOPE_GAPS else []
        if identifier == "FR-05":
            concerns.append("The catalog labels the solution claimed, and the Challenge boundary is marked pending independent review.")
        status = metadata(text, "Status", "Unknown")
        entries.append({
            "id": identifier,
            "title": text.splitlines()[0][len(title_prefix):],
            "status": status,
            "historical_difficulty": metadata(text, "Difficulty"),
            "canonical_path": path,
            "canonical_sha256": source_hash,
            "published_sha256": base_hash,
            "canonical_unchanged_from_base": base_hash == source_hash,
            "published_source_url": f"{REPOSITORY}/blob/{base}/{path}" if base_hash else None,
            "classification": classification,
            "local_project": project.relative_to(root).as_posix() if challenge.is_file() else None,
            "local_statement_path": challenge.relative_to(root).as_posix() if challenge.is_file() else None,
            "solution_source_present": solution.is_file(),
            "local_sources": {p.relative_to(root).as_posix(): sha256(p.read_bytes()) for p in local_imports(project)},
            "external_project": external,
            "campaign": campaign,
            "exactness_concerns": concerns,
            "completeness": "known-scope-gap" if identifier in SCOPE_GAPS else "not-independently-assessed-by-inventory",
            "proof_verification": "not-run-by-inventory",
            "statement_complexity_estimate": complexity_estimate(text),
        })
    counts = Counter(entry["classification"] for entry in entries)
    backlog = [entry for entry in entries if entry["classification"] in {"missing-statement", "local-scope-gap"}]
    by_status = Counter(entry["status"] for entry in backlog)
    return {
        "schema_version": 1,
        "base_commit": base,
        "registry_sha256": sha256((root / "problem_ids.json").read_bytes()),
        "method": "Canonical registry plus live Challenge/Solution imports and explicit shared campaign metadata; archive trees are not scanned.",
        "limitations": "Source existence, catalog status, and recorded review phases do not certify mathematical fidelity or kernel verification.",
        "counts": {"registered": len(entries), "classification": dict(sorted(counts.items())),
                   "statement_backlog_by_status": dict(sorted(by_status.items()))},
        "entries": entries,
    }


def render_coverage(inventory):
    counts = inventory["counts"]
    lines = ["# Lean statement coverage", "", f"Published base: `{inventory['base_commit']}`.", "",
             "This generated source inventory covers every permanent registered ID. It does not certify proofs, "
             "compilation, or mathematical fidelity. Catalog statuses are retained verbatim. "
             "A solution file's existence is not evidence that the original target is proved.", "",
             f"Registered entries: **{counts['registered']}**.", ""]
    lines += [f"- {key}: **{value}**" for key, value in counts["classification"].items()]
    lines += ["", "The six existing scope gaps remain explicit even when a new shared statement is recorded. "
              "IE-01, TR-01, MI-15, MI-18, and MI-32 already cite pinned external formalizations and are tracked separately "
              "from entries with no Lean statement. Copied historical and review projects do not count.", "",
              "Regenerate with `python3 tools/statement_inventory.py --base-ref <published-commit>`; "
              "add `--check` to reject stale generated files. The base commit is explicit so unrelated "
              "working-branch commits do not change the inventory.", "",
              "| ID | Status | Statement source | Exactness concerns |", "| --- | --- | --- | --- |"]
    for entry in inventory["entries"]:
        source = f"[{entry['id']}](../../../{entry['canonical_path']})"
        concerns = " ".join(entry["exactness_concerns"]).replace("|", "\\|") or "Not audited here."
        lines.append(f"| {source} | {entry['status']} | {entry['classification']} | {concerns} |")
    lines += ["", "## Statement-author work order", "",
              "Within each status, finite explicit assertions can share basic matrix definitions. "
              "Computational, probabilistic, and algebraic-geometric targets require concrete models; "
              "uninterpreted predicates are not complete replacements for those targets.", ""]
    for status in ("Solved", "Partially resolved", "Open"):
        entries = [e for e in inventory["entries"] if e["status"] == status and
                   e["classification"] in {"missing-statement", "local-scope-gap"}]
        lines.append(f"- **{status} ({len(entries)}):** " + ", ".join(e["id"] for e in entries) + ".")
    return "\n".join(lines) + "\n"


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--base-ref", required=True, help="Published git ref or immutable commit")
    parser.add_argument("--check", action="store_true", help="Fail if generated inventory or coverage is stale")
    args = parser.parse_args(argv)
    try:
        inventory = build_inventory(args.root, args.base_ref)
        outputs = {OUTPUT: json.dumps(inventory, ensure_ascii=False, indent=2) + "\n",
                   COVERAGE: render_coverage(inventory)}
        for relative, expected in outputs.items():
            path = args.root / relative
            if args.check:
                if not path.is_file() or path.read_text(encoding="utf-8") != expected:
                    raise ValueError(f"Stale generated inventory: {relative}")
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(expected, encoding="utf-8")
        print(json.dumps(inventory["counts"], sort_keys=True))
        return 0
    except (ValueError, OSError, json.JSONDecodeError) as error:
        print(f"statement inventory: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
