#!/usr/bin/env python3
"""Author preservation/source-copy audit, not a Lean or independent review.

Python 3.11+, git, and both immutable commits must be available locally.
Example: python3 audit_package.py --root /path/to/repo --output /tmp/audit.json
This command reads the repository and writes only the requested JSON report.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

BASE = "5487945e5a72abd952b0c89915915de8cc9b3e65"
CHECKPOINT = "353ebcfcbbcfc08184c32f391ecb6068c7d9098f"
PACKET = "docs/lean/proofs/IE-22/campaign-2026-10-23/preproof"
CANONICAL = "linear-systems-and-elimination/IE-22/lean"
README = "linear-systems-and-elimination/IE-22/README.md"
LOCK_SHA = "26fe6dce1658d183be3629094b83ea58e3c11aeb721566c4dd2711372906aad5"
CHALLENGE_SHA = "bd20cbb3d4495ff312192ab29fe7722463c8b74861f0a00ae83dd9b98ed4ec79"
TOOLCHAIN = "leanprover/lean4:v4.33.1\n"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
LEANCERT = "621a43d7cf21f87872392a01e874f2f1dbddc926"
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
ENDPOINTS = [
    "NLA.Proofs.IE22.uniform_squared_upper",
    "NLA.Proofs.IE22.near_sharp_unit_row_witness",
    "NLA.Proofs.IE22.target",
]
PROOFS = [
    "Assembly", "EnergyBounds", "ExtremaBounds", "Final", "FiniteSamples",
    "GaussianBasics", "GaussianCovariance", "GaussianNormBounds",
    "GaussianTrimming", "GaussianUpperBounds", "GaussianUpperRealization",
    "LowerWitness", "NormalizedGaussianApprox", "NormalizedGaussianRows",
    "SpectralProjection", "TrimmingDual", "UniformFiniteSamples",
    "UniversalUpper", "UpperParameters",
]
COPIES = [
    "NLA/Statements/Infrastructure.lean", "NLA/Statements/RowDeletion.lean",
    "NLA/Statements/IE22.lean", "Reviewed/IE22.lean",
] + [f"NLA/Proofs/IE22/{name}.lean" for name in PROOFS]
# These live files intentionally replace scaffold descriptions/configuration;
# their complete originals must survive both the frozen packet and text archive.
REFRESHED = {
    "BLOCKERS.md", "Challenge.lean", "README.md", "SPEC.md",
    "STATEMENT_REVIEW.md", "Solution.lean", "comparator.json",
    "formalization.yaml", "lake-manifest.json", "lakefile.toml",
}
BANNED = re.compile(r"\b(?:axiom|sorry|admit|unsafe|native_decide|implemented_by|extern)\b")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def lean_code(text: str) -> str:
    """Erase nested Lean comments and strings, retaining line boundaries.

    This is a deliberately limited lexical source guard. Kernel axiom closure,
    elaborated statement identity, and external library trust need Lean replay.
    """
    out = []
    i = 0
    depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end == -1:
                end = len(text)
            out.extend(" " * (end - i))
            i = end
        elif text[i] == '"':
            out.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    out.extend("  ")
                    i += 2
                elif text[i] == '"':
                    out.append(" ")
                    i += 1
                    break
                else:
                    out.append("\n" if text[i] == "\n" else " ")
                    i += 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError("unterminated nested Lean comment")
    return "".join(out)


def imports(text: str) -> list[str]:
    code = lean_code(text)
    result = []
    for line in code.splitlines():
        match = re.match(r"\s*import\s+(.+?)\s*$", line)
        if match:
            names = match.group(1).split()
            if not all(re.fullmatch(r"[\w.]+", name) for name in names):
                raise ValueError(f"unrecognized import syntax: {line}")
            result.extend(names)
    return result


def theorem_header(text: str, name: str) -> str:
    code = lean_code(text)
    match = re.search(r"\btheorem\s+" + re.escape(name) + r"\b(.*?)\s*:=", code, re.S)
    if not match:
        raise ValueError(f"missing theorem header {name}")
    return " ".join(match.group(0).split())


class Audit:
    def __init__(self, root: Path):
        self.root = root
        self.checks: list[dict] = []
        self.sources: list[dict] = []

    def check(self, name: str, ok: bool, **details):
        self.checks.append({"check": name, "pass": bool(ok), **details})

    def read(self, relative: str) -> bytes:
        return (self.root / relative).read_bytes()

    def git(self, revision: str, relative: str) -> bytes:
        return subprocess.run(
            ["git", "show", f"{revision}:{relative}"], cwd=self.root,
            check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        ).stdout

    def group(self, name, action):
        try:
            action()
        except Exception as exc:
            self.check(name, False, error=f"{type(exc).__name__}: {exc}")

    def source_copies(self):
        self.check("exactly_23_expected_shared_modules", len(COPIES) == 23)
        actual = {
            str(p.relative_to(self.root / CANONICAL))
            for prefix in ["NLA", "Reviewed"]
            for p in (self.root / CANONICAL / prefix).rglob("*.lean")
        }
        self.check("canonical_module_set_exact", actual == set(COPIES),
                   unexpected=sorted(actual - set(COPIES)), missing=sorted(set(COPIES) - actual))
        for rel in COPIES:
            published = self.git(CHECKPOINT, f"lean-statements/{rel}")
            shared = self.read(f"lean-statements/{rel}")
            canonical = self.read(f"{CANONICAL}/{rel}")
            self.check(f"shared_canonical_checkpoint_identity:{rel}",
                       published == shared == canonical, sha256=digest(shared),
                       canonical_sha256=digest(canonical), checkpoint_sha256=digest(published))
            self.sources.append({"module": rel[:-5].replace("/", "."), "sha256": digest(shared)})

    def original_inputs(self):
        lock_bytes = self.read(f"{PACKET}/INPUT_LOCK.json")
        self.check("input_lock_preapproved_bytes", digest(lock_bytes) == LOCK_SHA and
                   lock_bytes == self.git(CHECKPOINT, f"{PACKET}/INPUT_LOCK.json"), sha256=digest(lock_bytes))
        lock = json.loads(lock_bytes)
        entries = lock["reviewed_inputs"]
        self.check("original_32_input_count_and_base", len(entries) == 32 and
                   len({e['path'] for e in entries}) == 32 and lock['published_base'] == BASE)
        for entry in entries:
            rel = entry["path"]
            original = self.git(BASE, rel)
            snapshot = self.read(f"{PACKET}/frozen/{rel}")
            valid = len(original) == entry["bytes"] and digest(original) == entry["sha256"]
            self.check(f"base_and_snapshot:{rel}", valid and snapshot == original,
                       expected_sha256=entry["sha256"], base_sha256=digest(original),
                       snapshot_sha256=digest(snapshot))
            leaf = rel.removeprefix(f"{CANONICAL}/")
            if rel.startswith(f"{CANONICAL}/") and leaf in REFRESHED:
                archive_rel = f"{CANONICAL}/original-scaffold/{leaf}.txt"
                self.check(f"original_text_archive:{leaf}", self.read(archive_rel) == original,
                           archive=archive_rel)
            elif rel == README:
                # Verified promotion may replace the Lean-progress paragraph,
                # while the original target, credit and historical audits must
                # stay byte-identical and the whole original remains archived.
                current = self.read(rel)
                original_text = original.decode()
                current_text = current.decode()
                marker = "## Lean formalization scaffold\n"
                target = "## Problem statement\n"
                before, tail = original_text.split(marker, 1)
                _, after = tail.split(target, 1)
                self.check("canonical_readme_original_content_preserved",
                           current_text.startswith(before) and target + after in current_text)
            else:
                self.check(f"unrefreshed_input_unchanged:{rel}", self.read(rel) == original)
        for p in sorted((self.root / CANONICAL / "original-scaffold").glob("*.txt")):
            leaf = p.name.removesuffix(".txt")
            self.check(f"every_text_archive_is_exact:{leaf}",
                       p.read_bytes() == self.git(BASE, f"{CANONICAL}/{leaf}"))
        original_readme = self.git(BASE, README)
        for path in ["linear-systems-and-elimination/IE-22/ORIGINAL.md",
                     "docs/lean/statements/IE-22/ORIGINAL.md"]:
            self.check(f"complete_original_readme:{path}", self.read(path) == original_readme)

    def ids(self):
        current = self.read("problem_ids.json")
        base = self.git(BASE, "problem_ids.json")
        ids = json.loads(current)
        self.check("all_217_ids_paths_byte_identical", current == base and len(ids) == 217,
                   registry_sha256=digest(current), count=len(ids))
        self.check("IE22_permanent_path", ids.get("IE-22") == README)
        missing = [v for v in ids.values() if not (self.root / v).is_file()]
        self.check("all_217_canonical_paths_exist", not missing, missing=missing)

    def statements_and_comparator(self):
        challenge = self.read(f"{CANONICAL}/Challenge.lean")
        approved = self.read(f"{PACKET}/Challenge.lean")
        self.check("challenge_byte_exact_preapproved", challenge == approved and digest(challenge) == CHALLENGE_SHA,
                   sha256=digest(challenge))
        names = re.findall(r"\btheorem\s+([\w.]+)", lean_code(challenge.decode()))
        self.check("exact_three_challenge_names", names == [n.rsplit('.', 1)[1] for n in ENDPOINTS], names=names)
        locations = ["UniversalUpper", "LowerWitness", "Final"]
        for full_name, module in zip(ENDPOINTS, locations):
            name = full_name.rsplit(".", 1)[1]
            implementation = self.read(f"{CANONICAL}/NLA/Proofs/IE22/{module}.lean").decode()
            self.check(f"literal_endpoint_header:{name}",
                       theorem_header(challenge.decode(), name) == theorem_header(implementation, name))
        definitions = self.read(f"{CANONICAL}/Definitions.lean")
        self.check("old_definitions_preserved_byte_exact", definitions == self.git(BASE, f"{CANONICAL}/Definitions.lean"))
        original_solution = self.git(BASE, f"{CANONICAL}/Solution.lean").decode()
        solution = self.read(f"{CANONICAL}/Solution.lean").decode()
        for name in ["l2Sq_zero", "rowEnergy_empty"]:
            self.check(f"old_support_theorem_header:{name}",
                       theorem_header(original_solution, name) == theorem_header(solution, name))
            self.check(f"old_support_kernel_guard:{name}",
                       f"#assert_trust kernel IE22.{name}" in solution)
        cmp = json.loads(self.read(f"{CANONICAL}/comparator.json"))
        expected = {"challenge_module": "Challenge", "solution_module": "Solution",
                    "theorem_names": ENDPOINTS, "definition_names": [], "permitted_axioms": AXIOMS}
        self.check("comparator_exact_all3_no_defs_standard3", cmp == expected, actual=cmp)

    def pins(self):
        package = self.root / CANONICAL
        self.check("exact_lean_toolchain", (package / 'lean-toolchain').read_text() == TOOLCHAIN)
        manifest = json.loads((package / 'lake-manifest.json').read_bytes())
        original = json.loads(self.git(BASE, f"{CANONICAL}/lake-manifest.json"))
        # Mathlib was inherited in the scaffold and is now an explicit exact
        # requirement. Ordering and this resolution metadata can change without
        # changing any dependency checkout. Check every actual checkout field.
        checkout_keys = ['name', 'url', 'type', 'subDir', 'scope', 'rev', 'manifestFile', 'configFile']
        checkouts = lambda data: {
            p['name']: {k: p[k] for k in checkout_keys} for p in data['packages']}
        self.check("all_10_manifest_dependency_checkouts_immutable",
                   len(manifest['packages']) == len(original['packages']) == 10 and
                   checkouts(manifest) == checkouts(original))
        pins = {p['name']: p['rev'] for p in manifest['packages']}
        self.check("exact_mathlib_leancert_revisions", pins.get('mathlib') == MATHLIB and pins.get('leancert') == LEANCERT)
        direct = {p['name']: (p['inputRev'], p['inherited'])
                  for p in manifest['packages'] if p['name'] in ['mathlib', 'leancert']}
        self.check("direct_dependencies_resolve_exact_input_revisions", direct == {
            'mathlib': (MATHLIB, False), 'leancert': (LEANCERT, False)})
        lake = tomllib.loads((package / 'lakefile.toml').read_text())
        requires = {p['name']: (p['git'], p['rev']) for p in lake['require']}
        self.check("lake_requires_only_exact_pins", requires == {
            'mathlib': ('https://github.com/leanprover-community/mathlib4.git', MATHLIB),
            'leancert': ('https://github.com/alerad/leancert', LEANCERT)})
        metadata = json.loads((package / 'formalization.yaml').read_bytes())
        self.check("metadata_exact_toolchain", metadata['toolchain'] == {
            'lean': TOOLCHAIN.strip(), 'mathlib': MATHLIB, 'leancert': LEANCERT,
            'dependency_manifest': 'lake-manifest.json'})

    def solution_closure(self):
        self.check("lexical_guard_selftests",
                   BANNED.search(lean_code('/- axiom /- sorry -/ unsafe -/\n-- native_decide\n"admit"')) is None
                   and BANNED.search(lean_code('theorem x : True := by sorry')) is not None
                   and BANNED.search(lean_code('axiom x : True')) is not None)
        visited = set()
        external = set()
        todo = ['Solution']
        while todo:
            module = todo.pop()
            if module in visited:
                continue
            visited.add(module)
            rel = f"{CANONICAL}/{module.replace('.', '/')}.lean"
            text = self.read(rel).decode()
            code = lean_code(text)
            found = [{"token": m.group(0), "line": code.count('\n', 0, m.start()) + 1}
                     for m in BANNED.finditer(code)]
            self.check(f"solution_closure_forbidden_tokens:{module}", not found, occurrences=found)
            self.check(f"solution_closure_no_challenge_reference:{module}",
                       re.search(r"\b(?:[\w]+\.)*Challenge\b", code) is None)
            for imported in imports(text):
                self.check(f"no_challenge_import:{module}:{imported}",
                           not (imported == 'Challenge' or imported.endswith('.Challenge')))
                local = self.root / CANONICAL / (imported.replace('.', '/') + '.lean')
                if local.is_file():
                    todo.append(imported)
                else:
                    external.add(imported)
                    self.check(f"external_import_is_pinned_library:{module}:{imported}",
                               imported == 'Mathlib' or imported.startswith('Mathlib.') or
                               imported == 'Lean' or imported.startswith('Lean.') or
                               imported.startswith('LeanCert.'))
        expected = {'Solution', 'Definitions', 'NLA.Statements.IE22',
                    'NLA.Statements.RowDeletion', 'NLA.Statements.Infrastructure'} | {
                        'NLA.Proofs.IE22.' + n for n in PROOFS}
        self.check("actual_24_module_solution_closure_exact", visited == expected,
                   modules=sorted(visited), external_pinned_imports=sorted(external))
        for name in PROOFS:
            text = self.read(f"{CANONICAL}/NLA/Proofs/IE22/{name}.lean").decode()
            self.check(f"explicit_kernel_mode_and_guard:{name}",
                       'set_option leancert.trust "kernel"' in text and '#assert_trust kernel ' in text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True, help='Repository checkout containing both immutable git objects')
    parser.add_argument('--output', type=Path, required=True, help='JSON report file; only this output is written')
    args = parser.parse_args()
    audit = Audit(args.root.resolve())
    for label, method in [
        ('source_copies', audit.source_copies), ('original_inputs', audit.original_inputs),
        ('permanent_ids', audit.ids), ('statements_and_comparator', audit.statements_and_comparator),
        ('dependency_pins', audit.pins), ('solution_import_closure', audit.solution_closure),
    ]:
        audit.group(label, method)
    passed = all(c['pass'] for c in audit.checks)
    report = {
        'audit_kind': 'author static preservation/source-copy audit; not kernel replay, independent review, Comparator execution, or CI',
        'root': str(audit.root), 'published_base': BASE, 'immutable_proof_checkpoint': CHECKPOINT,
        'script_sha256': digest(Path(__file__).read_bytes()), 'pass': passed,
        'checks_total': len(audit.checks), 'checks_failed': sum(not c['pass'] for c in audit.checks),
        'sources': audit.sources, 'checks': audit.checks,
        'limitations': [
            'The source scanner is a lexical guard on the 24 own modules in Solution closure, not a Lean elaborator.',
            'External imports are covered by exact dependency pins and require independent fresh Lean kernel replay.',
            'Successful source/header checks do not replace elaborated Comparator identity or axiom-closure execution.',
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({k: report[k] for k in ['pass', 'checks_total', 'checks_failed', 'script_sha256']}))
    for item in audit.checks:
        if not item['pass']:
            print(json.dumps(item, ensure_ascii=False))
    return 0 if passed else 1


if __name__ == '__main__':
    sys.exit(main())
