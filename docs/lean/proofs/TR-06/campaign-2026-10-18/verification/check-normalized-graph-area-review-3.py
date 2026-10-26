#!/usr/bin/env python3
"""Freeze/build local import closure and audit every explicit TR06 declaration.

Uses fresh output objects, never campaign .lake objects. Dependencies are pinned
cached Mathlib/LeanCert objects; this is a local kernel audit, not Linux Comparator.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

REPO = Path(__file__).resolve().parents[6]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--project", type=Path, default=REPO / "lean-statements")
parser.add_argument("--evidence-name", default="support-review")
parser.add_argument("--top", nargs="+", default=["RealAdditionProperness"])
parser.add_argument("--root-module", nargs="+", help="Complete module names, e.g. Solution Identity")
parser.add_argument("--target-theorem", help="Require this theorem's literal type to be the unchanged TR06 Target")
parser.add_argument("--build-only-module", nargs="+", default=[], help="Freeze/build without importing or auditing their deliberate Challenge placeholder")
args = parser.parse_args()
if Path(args.evidence_name).name != args.evidence_name:
    parser.error("--evidence-name must be a single directory name")
EVIDENCE = Path(__file__).with_name(args.evidence_name)
PROJECT = args.project.resolve()
LEAN = Path("/private/tmp/pf05-tooling/elan-home/toolchains/leanprover--lean4---v4.33.1/bin/lean")
PACKAGES = PROJECT / ".lake/packages"
TOP = args.top
ROOT_MODULES = args.root_module or ["NLA.Proofs.TR06." + name for name in TOP]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def run(argv, **kwargs):
    proc = subprocess.run(list(map(str, argv)), text=True, capture_output=True, **kwargs)
    return {"argv": list(map(str, argv)), "exit_code": proc.returncode,
            "stdout": proc.stdout, "stderr": proc.stderr}


def dependencies():
    records = []
    for item in json.loads((PROJECT / "lake-manifest.json").read_text())["packages"]:
        directory = PACKAGES / item["name"]
        head = run(["git", "-C", directory, "rev-parse", "HEAD"])
        status = run(["git", "-C", directory, "status", "--porcelain", "--untracked-files=no"])
        records.append({"name": item["name"], "expected_revision": item["rev"],
                        "directory": str(directory), "head": head, "status": status,
                        "passed": head["exit_code"] == status["exit_code"] == 0
                        and head["stdout"].strip() == item["rev"] and not status["stdout"].strip()})
    if not all(item["passed"] for item in records):
        raise RuntimeError("Dependency pins/cleanliness failed")
    return records


def without_comments(text):
    """Strip nested Lean block comments and line comments, retaining line numbers."""
    result = []
    depth = 0
    for line in text.splitlines():
        clean = []
        i = 0
        while i < len(line):
            pair = line[i:i+2]
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/" and depth:
                depth -= 1
                i += 2
            elif pair == "--" and not depth:
                break
            else:
                if not depth:
                    clean.append(line[i])
                i += 1
        result.append("".join(clean))
    if depth:
        raise RuntimeError("Unclosed source comment")
    return "\n".join(result)


frozen = {}
visiting = set()


def freeze(module):
    name = module.replace(".", "/") + ".lean"
    if name in frozen:
        return
    if name in visiting:
        raise RuntimeError("Cyclic local imports: " + name)
    visiting.add(name)
    data = (PROJECT / name).read_bytes()
    for line in without_comments(data.decode()).splitlines():
        match = re.fullmatch(r"import\s+([A-Za-z0-9_.]+)\s*", line)
        if match and (PROJECT / (match[1].replace(".", "/") + ".lean")).is_file():
            freeze(match[1])
    frozen[name] = data
    visiting.remove(name)


for module in ROOT_MODULES + args.build_only_module:
    freeze(module)


def declarations_of(name, data):
    """Track namespace components and named sections, not just a fixed prefix."""
    scopes = []
    declarations = []
    for number, line in enumerate(without_comments(data.decode()).splitlines(), 1):
        if line.startswith("namespace "):
            for part in line.split()[1].split("."):
                scopes.append(("namespace", part))
        elif re.match(r"^(?:noncomputable\s+)?section(?:\s|$)", line):
            section_parts = re.sub(r"^noncomputable\s+", "", line).split()
            scopes.append(("section", section_parts[1] if len(section_parts) > 1 else ""))
        elif re.match(r"^end(?:\s|$)", line):
            parts = line.split()[1:]
            count = len(parts[0].split(".")) if parts else 1
            for _ in range(count):
                if not scopes:
                    raise RuntimeError(f"Unbalanced scope at {name}:{number}")
                scopes.pop()
        match = re.match(r"^(?:@\[[^\n]*\]\s*)?(?:local\s+)?(?P<private>private\s+)?(?:noncomputable\s+)?"
                         r"(theorem|lemma|def|abbrev|instance|inductive|structure|opaque|axiom)\s+"
                         r"([A-Za-z_][A-Za-z0-9_.']*)", line)
        if match:
            private, kind, declaration = match.groups()
            prefix = ".".join(part for kind, part in scopes if kind == "namespace")
            declarations.append({"name": prefix + "." + declaration, "kind": kind,
                                 "source": name, "line": number,
                                 "visibility": ("private" if private else "local" if line.startswith("local ") else "public")})
            if private and kind not in {"theorem", "lemma", "def", "abbrev"}:
                raise RuntimeError("Private non-theorem requires an explicit audit implementation: " + name)
        if re.match(r"^protected\s+", line):
            raise RuntimeError("Unsupported declaration modifier requires explicit audit: " + name)
    if any(kind == "namespace" for kind, _ in scopes):
        raise RuntimeError("Unclosed namespace: " + name)
    # Lean permits file-scoped sections to close implicitly at EOF. They do
    # not change qualified constant names; namespace balance remains strict.
    return declarations


declarations = [d for name, data in frozen.items() if "/Proofs/" in name or name.startswith("NLA/TR06/") or name in {"Solution.lean", "Identity.lean"}
                for d in declarations_of(name, data)]
audit = "\n".join("import " + name for name in ROOT_MODULES) + '''
import LeanCert.Tactic.Verification
open Lean Elab Command in
elab "#assert_proof_constant " n:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  match (← getEnv).find? decl with
  | some (.thmInfo _) => pure ()
  | _ => throwErrorAt n "expected a proved theorem constant"
open Lean Elab Command in
elab "#assert_internal_constant " mod:str suffix:str expected:str : command => do
  let declPrefix := "_private." ++ mod.getString ++ "."
  let ending := "." ++ suffix.getString
  let candidates := (← getEnv).constants.toList.filter fun (n, _) =>
    n.toString == suffix.getString || (n.toString.startsWith declPrefix && n.toString.endsWith ending)
  unless candidates.length == 1 do
    throwError "expected exactly one actual private declaration"
  let some (decl, info) := candidates.head? | throwError "private declaration missing"
  match expected.getString, info with
  | "theorem", .thmInfo _ => pure ()
  | "definition", .defnInfo _ => pure ()
  | _, _ => throwError "private declaration kind does not match its source"
  logInfo m!"INTERNAL_CONSTANT {decl} KIND={expected.getString}"
  let declIdent := mkIdent decl
  elabCommand (← `(#assert_trust $(mkIdent `kernel):ident $declIdent:ident))
  elabCommand (← `(#print axioms $declIdent:ident))
'''
for declaration in declarations:
    name = declaration["name"]
    if declaration["visibility"] in {"private", "local"}:
        module = declaration["source"][:-5].replace("/", ".")
        expected = "theorem" if declaration["kind"] in {"theorem", "lemma"} else "definition"
        audit += f'#assert_internal_constant "{module}" "{name}" "{expected}"\n'
        continue
    if declaration["kind"] in {"theorem", "lemma"}:
        audit += f"#assert_proof_constant {name}\n"
    audit += f"#assert_trust kernel {name}\n#print axioms {name}\n"
if args.target_theorem:
    audit += '''open Lean Elab Command in
elab "#assert_literal_tr06_target " n:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  match (← getEnv).find? decl with
  | some (.thmInfo info) =>
    unless info.type == mkConst ``NLA.Statements.TR06.Target do
      throwErrorAt n "expected the literal unchanged TR06 Target, without parameters"
  | _ => throwErrorAt n "expected a proved theorem constant"
'''
    audit += (f"#assert_literal_tr06_target {args.target_theorem}\n"
              f"#assert_trust kernel {args.target_theorem}\n"
              f"#print axioms {args.target_theorem}\n")
frozen["IndependentTreeColorAudit.lean"] = audit.encode()
EVIDENCE.mkdir(exist_ok=True)
(EVIDENCE / "audit-driver.py.txt").write_bytes(Path(__file__).read_bytes())
for name, data in frozen.items():
    target = EVIDENCE / "source" / (name + ".txt")
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
retained_lock = json.loads((REPO / "docs/lean/proofs/TR-06/campaign-2026-10-18/retained-58-source-lock.json").read_text())
def retained_identity():
    return {item["campaign_path"]: sha((REPO / item["campaign_path"]).read_bytes()) == item["sha256"]
            for item in retained_lock["records"]}
retained_before = retained_identity()
if not all(retained_before.values()):
    raise RuntimeError("Retained 58-source baseline changed before audit")
result = {
    "scope": ("Fresh-source local macOS kernel audit of the full unchanged frozen TR06 Target and its complete local import closure"
              if args.target_theorem else "Fresh-source local TR06 actual annular volume and angular integral bounded by literal normalized graph Hausdorff volume support audit; no proved finite graph volume or full TR06 Target claim"),
    "reviewer": "/root/lean_verification (AI agent)",
    "self_authored_TR06_modules": [],
    "reviewer_authored_retained_TR06_sources": [],
    "declaration_coverage": "Every explicit named theorem/lemma/def/abbrev/instance/inductive/structure/opaque/axiom in frozen TR06 proof modules and selected package exports; retained model Definitions explicitly checked; statement definitions and generated helper constants checked transitively",
    "top_modules": TOP, "root_modules": ROOT_MODULES,
    "build_only_modules_excluded_from_proof_consumer": args.build_only_module, "project_root": str(PROJECT),
    "exact_target_theorem": args.target_theorem,
    "source_sha256": {name: sha(data) for name, data in frozen.items()},
    "audit_driver_sha256": sha(Path(__file__).read_bytes()),
    "declarations": declarations,
    "proof_theorem_count": sum(d["kind"] in {"theorem", "lemma"} for d in declarations),
    "lean_version": run([LEAN, "--version"]), "lean_sha256": sha(LEAN.read_bytes()),
    "dependencies_before": dependencies(), "retained_58_before": retained_before, "commands": [],
    "authoritative_linux_comparator": False, "full_tr06_target_proved": False,
}
try:
    with tempfile.TemporaryDirectory(prefix="nla-pf05-tree-color-audit-") as temporary:
        root = Path(temporary)
        sources, outputs = root / "source", root / "output"
        for name, data in frozen.items():
            target = sources / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        outputs.mkdir()
        libs = [path / ".lake/build/lib/lean" for path in sorted(PACKAGES.iterdir())
                if (path / ".lake/build/lib/lean").is_dir()]
        env = dict(os.environ, LEAN_PATH=":".join(map(str, [outputs, *libs, LEAN.parent.parent / "lib/lean"])))
        result["lean_path"] = env["LEAN_PATH"]
        for name in frozen:
            out = outputs / Path(name).with_suffix(".olean")
            out.parent.mkdir(parents=True, exist_ok=True)
            record = run([LEAN, "-R", sources, "-o", out, sources / name], cwd=sources, env=env, timeout=180)
            record["source"] = name
            result["commands"].append(record)
            (EVIDENCE / (name.replace("/", "-") + ".log")).write_text(record["stdout"] + record["stderr"])
            print(f"{name}: {record['exit_code']}", flush=True)
            if record["exit_code"]:
                break
except Exception as error:
    result["exception"] = repr(error)
result["dependencies_after"] = dependencies()
result["retained_58_after"] = retained_identity()
result["source_unchanged_after"] = {name: (PROJECT / name).read_bytes() == data
                                    for name, data in frozen.items() if name != "IndependentTreeColorAudit.lean"}
result["passed"] = (len(result["commands"]) == len(frozen)
                    and all(item["exit_code"] == 0 for item in result["commands"])
                    and all(result["source_unchanged_after"].values())
                    and all(result["retained_58_after"].values())
                    and "exception" not in result)
result["full_tr06_target_proved"] = bool(args.target_theorem and result["passed"])
(EVIDENCE / "result.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"passed": result["passed"], "evidence": str(EVIDENCE),
                  "proof_theorem_count": result["proof_theorem_count"],
                  "audited_exports": len(declarations), "source_count": len(frozen)}, indent=2))
raise SystemExit(0 if result["passed"] else 1)
