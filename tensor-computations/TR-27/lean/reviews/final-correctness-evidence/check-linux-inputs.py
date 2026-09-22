#!/usr/bin/env python3
"""Independent reviewer input/log cross-check; does not execute Lean or the sandbox."""
from pathlib import Path
import hashlib, json, re, subprocess, tarfile

package = Path(__file__).resolve().parents[2]
repo = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], cwd=package, text=True).strip())
evidence = package / "verification/linux"
sha = lambda data: hashlib.sha256(data).hexdigest()
read = lambda name: json.loads((evidence / name).read_text())
result = read("successful-verification/result.json")
inputs = read("input-receipt.json")
commit = "775e8b169119c4045b07db7666eda8c001ae3bd1"
project = "tensor-computations/TR-27/lean"
listed = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", commit, "--", project], cwd=repo, text=True).splitlines()
committed = {str(Path(name).relative_to(project)): sha(subprocess.check_output(["git", "show", f"{commit}:{name}"], cwd=repo)) for name in listed}
retained = {str(path.relative_to(evidence / "source")): sha(path.read_bytes()) for path in (evidence / "source").rglob("*") if path.is_file()}
assert len(committed) == 116
assert committed == retained == result["input_sha256"] == inputs["input_sha256"]
old = json.loads((package / "reviews/final-correctness-evidence/source-review-receipt.json").read_text())
assert all(committed[name] == digest for name, digest in old["source_sha256"].items())
# Current status documents may subsequently change; mathematical inputs may not.
math_names = [name for name in committed if name.startswith("NLA/TR27/")] + ["Solution.lean", "Challenge.lean", "NUMERICAL_TARGETS.md", "comparator.json", "lakefile.toml", "lake-manifest.json", "lean-toolchain"]
assert all(sha((package / name).read_bytes()) == committed[name] for name in math_names)
with tarfile.open(evidence / "input.tar") as archive:
    archived = {str(Path(m.name).relative_to(project)): sha(archive.extractfile(m).read()) for m in archive.getmembers() if m.isfile()}
assert archived == committed
print("PASS: all 116 publication Git blobs equal result/input receipts, retained source and input archive")
print("PASS: all prior-review-bound files match the verified snapshot; current mathematical files unchanged")

names = result["config"]["theorem_names"]
assert len(names) == len(set(names)) == 25
assert result["config"] == json.loads((package / "comparator.json").read_text())
proof = (evidence / "successful-verification/comparator.log").read_text()
exports = re.findall(r"^Exporting #\[(.*)\] from (Challenge|Solution)$", proof, re.M)
assert [module for _, module in exports] == ["Challenge", "Solution"]
for line, module in exports:
    assert [name for name in line.split(", ") if name.startswith("NLA.TR27.")] == names
axioms = re.findall(r"^info: Solution\.lean:\d+:\d+: '([^']+)' depends on axioms: \[([^]]+)\]$", proof, re.M)
assert [name for name, _ in axioms] == names
assert all(set(ax.split(", ")) == {"propext", "Classical.choice", "Quot.sound"} for _, ax in axioms)
assert proof.rstrip().endswith("EXIT_STATUS=0")
assert "Lean default kernel accepts the solution" in proof
assert "Your solution is okay!" in proof
assert "Built LeanCert.Tactic.Verification" in proof
solution = (evidence / "source/Solution.lean").read_text()
assert re.findall(r"^#assert_trust kernel (\S+)$", solution, re.M) == names
assert re.findall(r"^#print axioms (\S+)$", solution, re.M) == names
print("PASS: exact 25 Challenge/Solution exports, Solution trust assertions and standard-axiom outputs; kernel acceptance")

auth = read("driver-authentication.json")
for name, digest in auth["sha256"].items():
    assert sha((repo / "tools/lean" / name).read_bytes()) == digest == sha((evidence / "checker-source" / name).read_bytes())
manifest = json.loads((evidence / "source/lake-manifest.json").read_text())
pins = {p["name"]: p["rev"] for p in manifest["packages"]}
deps = read("dependency-evidence/dependency-receipt.json")
assert len(pins) == 10
assert pins == {p["name"]: p["actual_git_head"] for p in deps["packages"]}
assert sha((evidence / "dependency-evidence/LeanCert-Verification.lean").read_bytes()) == deps["LeanCert_Verification_sha256"] == "2c576708b528acdde17796b0b715b83079f9cad377182dbd87c248323ff0a58c"
assert deps["LeanCert_Verification_bytes_match_pinned_git_blob"] is True
print("PASS: unchanged shared harness/source lock, 10 pinned dependency records, authenticated LeanCert source bytes")
