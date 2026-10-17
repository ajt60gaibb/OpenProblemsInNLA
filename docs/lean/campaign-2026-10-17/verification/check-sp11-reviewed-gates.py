#!/usr/bin/env python3
"""Fresh independent local build of the reviewed SP-11 conditional gates."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

REPO = Path(__file__).resolve().parents[4]
PROJECT = REPO / "lean-statements"
EVIDENCE = Path(__file__).with_name("sp11-gate-review")
LEAN = Path("/private/tmp/pf05-tooling/elan-home/toolchains/leanprover--lean4---v4.33.1/bin/lean")
PACKAGES = Path("/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages")
SOURCES = ["NLA/Statements/Infrastructure.lean", "NLA/Statements/SP11.lean",
           "NLA/Proofs/SP11/GramBridge.lean", "NLA/Proofs/SP11/PolynomialFaithfulness.lean"]
THEOREMS = ["gram_apply", "gram_hasPattern", "gram_rank_le", "minDegree_le_gram_nullity",
            "target_of_faithful_representations", "exists_real_eval_ne_zero",
            "exists_simultaneous_real_eval_ne_zero", "eval_polynomialGram",
            "exists_faithful_real_evaluation", "target_of_polynomial_representations"]


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
        records.append({"name": item["name"], "expected_revision": item["rev"], "directory": str(directory),
                        "head": head, "status": status,
                        "passed": head["exit_code"] == status["exit_code"] == 0
                        and head["stdout"].strip() == item["rev"] and not status["stdout"].strip()})
    if not all(item["passed"] for item in records):
        raise RuntimeError("Dependency pins/cleanliness failed")
    return records


EVIDENCE.mkdir(exist_ok=True)
frozen = {name: (PROJECT / name).read_bytes() for name in SOURCES}
audit = "import NLA.Proofs.SP11.PolynomialFaithfulness\nimport LeanCert.Tactic.Verification\n"
for name in THEOREMS:
    audit += f"#assert_trust kernel NLA.Proofs.SP11.{name}\n#print axioms NLA.Proofs.SP11.{name}\n"
frozen["IndependentAudit.lean"] = audit.encode()
for name, data in frozen.items():
    target = EVIDENCE / "source" / (name + ".txt")
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
result = {"scope": "Independent local macOS source build and all-export LeanCert kernel audit of conditional SP-11 gates only",
          "source_sha256": {name: sha(data) for name, data in frozen.items()},
          "reviewer": "/root/lean_verification (AI agent)",
          "lean_version": run([LEAN, "--version"]), "lean_sha256": sha(LEAN.read_bytes()),
          "dependencies_before": dependencies(), "commands": [],
          "authoritative_linux_comparator": False, "full_sp11_target_proved": False}
with tempfile.TemporaryDirectory(prefix="nla-sp11-independent-gate-review-") as temporary:
    root = Path(temporary)
    sources, outputs = root / "source", root / "output"
    for name, data in frozen.items():
        target = sources / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    outputs.mkdir()
    libs = [path / ".lake/build/lib/lean" for path in PACKAGES.iterdir() if (path / ".lake/build/lib/lean").is_dir()]
    env = dict(os.environ, LEAN_PATH=":".join(map(str, [outputs, *libs, LEAN.parent.parent / "lib/lean"])))
    for name in list(frozen):
        out = outputs / Path(name).with_suffix(".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        record = run([LEAN, "-R", sources, "-o", out, sources / name], cwd=sources, env=env, timeout=120)
        record["source"] = name
        result["commands"].append(record)
        (EVIDENCE / (name.replace("/", "-") + ".log")).write_text(record["stdout"] + record["stderr"])
        if record["exit_code"]:
            break
result["dependencies_after"] = dependencies()
result["source_unchanged_after"] = {name: (PROJECT / name).read_bytes() == data for name, data in frozen.items() if name in SOURCES}
result["passed"] = (len(result["commands"]) == 5 and all(item["exit_code"] == 0 for item in result["commands"])
                    and all(result["source_unchanged_after"].values()))
(EVIDENCE / "result.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"passed": result["passed"], "evidence": str(EVIDENCE), "source_sha256": result["source_sha256"]}, indent=2))
raise SystemExit(0 if result["passed"] else 1)
