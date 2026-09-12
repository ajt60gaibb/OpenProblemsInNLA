"""Independent source/statement/evidence audit; no claim of Linux execution."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

evidence = Path(__file__).resolve().parent
project = evidence.parents[1]
root = project.parents[2]
freeze = json.loads((project / "verification/proof-freeze.json").read_text())
for path, item in freeze["files"].items():
    assert hashlib.sha256((project / path).read_bytes()).hexdigest() == item["sha256"], path
for path, item in freeze["original_sources"].items():
    actual = (root / path).read_bytes()
    assert hashlib.sha256(actual).hexdigest() == item["sha256"], path
    assert actual == subprocess.check_output(["git", "show", f"{freeze['source_commit']}:{path}"], cwd=root)


def strip_comments(text):
    result, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif not depth and text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            if not depth:
                result.append(text[i])
            i += 1
    assert depth == 0
    return "".join(result)


challenge = strip_comments((project / "Challenge.lean").read_text())
solution = strip_comments((project / "Solution.lean").read_text())
matched = []
for qualified in freeze["public_exports"]:
    name = qualified.rsplit(".", 1)[1]
    pattern = rf"\btheorem\s+{re.escape(name)}\b(.*?)\s*:=\s*by"
    c = re.search(pattern, challenge, re.S)
    s = re.search(pattern, solution, re.S)
    assert c and s, name
    assert re.sub(r"\s+", "", c.group(1)) == re.sub(r"\s+", "", s.group(1)), name
    matched.append(qualified)

implementation = [p for p in freeze["files"] if p.endswith(".lean")
                  and (p.startswith("NLA/") or p == "Solution.lean")]
source_assertions = 0
for path in implementation:
    text = strip_comments((project / path).read_text())
    assert not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool|ofReduceNat|trustCompiler)\b", text), path
    assert not re.search(r"^\s*import\s+Challenge\b", text, re.M), path
    assert not re.search(r"^\s*(run_elab|run_cmd|#eval)\b", text, re.M), path
    source_assertions += text.count("#assert_trust kernel")
assert source_assertions == 12
config = json.loads((project / "comparator.json").read_text())
assert config["theorem_names"] == freeze["public_exports"]
assert config["definition_names"] == []
assert set(config["permitted_axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
execution = json.loads((evidence / "execution.json").read_text())
assert len(execution["commands"]) == 6
assert all(r["exit_code"] == 0 for r in execution["commands"])
axioms = json.loads((evidence / "axioms.json").read_text())
assert axioms["count"] == 12
inspection = (evidence / "inspection.log").read_text()
assert "ROOT_PROJECT_DECLARATION_COUNT: 62" in inspection
assert len(re.findall(r"^ROOT_RETAINED:", inspection, re.M)) == 14
assert "warning:" not in inspection and "error:" not in inspection

libraries = [".lake/packages/mathlib/Mathlib/Algebra/Polynomial/Derivative.lean",
             ".lake/packages/mathlib/Mathlib/Algebra/Polynomial/Splits.lean",
             ".lake/packages/mathlib/Mathlib/Analysis/Complex/Polynomial/GaussLucas.lean",
             ".lake/packages/leancert/LeanCert/Tactic/Verification.lean"]
report = {"status": "PASS: independent local final-proof audit; actual Linux still pending",
          "frozen_files_unchanged": len(freeze["files"]),
          "original_sources_unchanged": len(freeze["original_sources"]),
          "matched_public_signatures": matched, "implementation_sources_scanned": implementation,
          "kernel_source_assertions": source_assertions, "fresh_axiom_reports": axioms["count"],
          "fresh_modules": len(execution["commands"]), "project_declarations_traversed": 62,
          "required_retained_mathematical_dependencies": 14,
          "approved_LeanCert_scope": "Explicit kernel trust audits of exact algebra/root geometry; no artificial interval certificate",
          "library_sources_read_sha256": {p: hashlib.sha256((project/p).read_bytes()).hexdigest() for p in libraries}}
(evidence / "audit.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
