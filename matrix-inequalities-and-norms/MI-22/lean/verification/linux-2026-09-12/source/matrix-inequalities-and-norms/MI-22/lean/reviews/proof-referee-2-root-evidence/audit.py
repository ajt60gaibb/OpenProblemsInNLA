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
config = json.loads((project / "comparator.json").read_text())
original_sources = freeze["source_files"]
for path, item in freeze["files"].items():
    assert hashlib.sha256((project / path).read_bytes()).hexdigest() == item["sha256"], path
for path, item in original_sources.items():
    actual = (root / path).read_bytes()
    assert hashlib.sha256(actual).hexdigest() == item, path
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
for qualified in config["theorem_names"]:
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
assert source_assertions == 17
config = json.loads((project / "comparator.json").read_text())
assert config["definition_names"] == []
assert set(config["permitted_axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
execution = json.loads((evidence / "execution.json").read_text())
assert len(execution["commands"]) == 8
assert all(r["exit_code"] == 0 for r in execution["commands"])
axioms = json.loads((evidence / "axioms.json").read_text())
assert axioms["count"] == 17
inspection = (evidence / "inspection.log").read_text()
assert "PROJECT_DECLARATIONS: 195" in inspection
assert len(re.findall(r"^RETAINED_DEPENDENCY:", inspection, re.M)) == 21
assert "warning:" not in inspection and "error:" not in inspection

libraries = [".lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/SingularValues.lean",
             ".lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Basic.lean",
             ".lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean",
             ".lake/packages/mathlib/Mathlib/Analysis/Matrix/Normed.lean",
             ".lake/packages/leancert/LeanCert/Validity/DyadicBounds.lean"]
assert "of_decide_eq_true (id (Eq.refl true))" in inspection
assert "LT.lt.trans NLA.MI22.numerical_separation" in inspection
assert json.loads((evidence / "inspection.json").read_text())["exit_code"] == 0
statement = json.loads((project / "reviews/statement-freeze.json").read_text())
for name, expected in statement["files"].items():
    expected = expected["sha256"] if isinstance(expected, dict) else expected
    actual = project / ("verification/lakefile.statement.toml" if name == "lakefile.toml" else name)
    assert hashlib.sha256(actual.read_bytes()).hexdigest() == expected, name
registration = json.loads((project / "verification/build-registration.json").read_text())
assert (project / "lakefile.toml").read_text() == (project / "verification/lakefile.statement.toml").read_text() + registration["exact_append"]
assert registration["exact_append"] == '\n[[lean_lib]]\nname = "Solution"\n'
assert 'defaultTargets = ["Challenge"]' in (project / "lakefile.toml").read_text()
oldobjects = str((project / ".lake/build/lib/lean").resolve())
assert oldobjects not in execution["LEAN_PATH"].split(":")
assert json.loads((evidence / "dependencies.json").read_text())["status"] == "PASS"

report = {"status": "PASS: independent local final-proof audit; actual Linux still pending",
          "frozen_files_unchanged": len(freeze["files"]),
          "original_sources_unchanged": len(original_sources),
          "matched_public_signatures": matched, "implementation_sources_scanned": implementation,
          "kernel_source_assertions": source_assertions, "fresh_axiom_reports": axioms["count"],
          "fresh_modules": len(execution["commands"]), "project_declarations_traversed": 195,
          "required_retained_mathematical_dependencies": 21,
          "approved_LeanCert_scope": "Actual consumed strict-point certificate 10500<11000; full actual CFC, Euclidean norm, singular-value semantics, rational witness and first-prefix violation",
          "library_sources_read_sha256": {p: hashlib.sha256((project/p).read_bytes()).hexdigest() for p in libraries}}
(evidence / "audit.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
