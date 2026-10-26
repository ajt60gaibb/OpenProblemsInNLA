#!/usr/bin/env python3
"""Positive and negative fixture for exact-name private/local auditor behavior."""
from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, os, subprocess, tempfile

BASE = Path(__file__).resolve().parent
REPO = BASE.parents[5]
LEAN = REPO.parent / "tooling/lean-4.33.1-darwin_aarch64/bin/lean"
PACKAGES = (REPO / "lean-statements/.lake/packages").resolve()
out = BASE / "private-auditor-preflight"
out.mkdir(exist_ok=False)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
tree = ast.parse((BASE / "replay.py").read_text())
preamble = next(ast.literal_eval(n.value) for n in tree.body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "preamble" for t in n.targets))
fixture = '''import LeanCert.Tactic.Verification
set_option leancert.trust "kernel"
namespace IndependentAuditFixture
private theorem hidden : True := True.intro
local instance localProof : NeZero (1 : Nat) := ⟨by decide⟩
def visible : Nat := 1
axiom customAuditOnly : False
private theorem rejected : False := customAuditOnly
end IndependentAuditFixture
'''
positive = "import PrivateFixture\n" + preamble + '''
#audit_named "IndependentAuditFixture.hidden" "PrivateFixture" "private" "theorem"
#audit_named "IndependentAuditFixture.localProof" "PrivateFixture" "local" "theorem"
#audit_named "IndependentAuditFixture.visible" "PrivateFixture" "public" "definition"
'''
negative = "import PrivateFixture\n" + preamble + '''
#audit_named "IndependentAuditFixture.rejected" "PrivateFixture" "private" "theorem"
'''
sources = {"PrivateFixture.lean": fixture, "PrivatePositive.lean": positive, "PrivateNegative.lean": negative}
for name, data in sources.items(): (out / name).write_text(data)
commands = []
with tempfile.TemporaryDirectory(prefix="objects-", dir=BASE) as temporary:
    fresh = Path(temporary)
    libs = [p / ".lake/build/lib/lean" for p in sorted(PACKAGES.iterdir()) if (p / ".lake/build/lib/lean").is_dir()]
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [fresh, *libs, LEAN.parent.parent / "lib/lean"])))
    for name, expected in [("PrivateFixture.lean", 0), ("PrivatePositive.lean", 0), ("PrivateNegative.lean", 1)]:
        p = subprocess.run([str(LEAN), "-R", str(out), "-o", str(fresh / Path(name).with_suffix(".olean")), str(out / name)], env=env, cwd=out, capture_output=True, text=True)
        log = out / (name + ".log")
        log.write_text(p.stdout + p.stderr)
        commands.append({"source": name, "source_sha256": sha(out / name), "exit_code": p.returncode, "expected_exit_code": expected, "log": str(log.relative_to(REPO)), "log_sha256": sha(log)})
        assert p.returncode == expected, p.stdout + p.stderr
    positive_log = (out / "PrivatePositive.lean.log").read_text()
    assert "AUDITED_ACTUAL IndependentAuditFixture.hidden _private.PrivateFixture.0.IndependentAuditFixture.hidden private" in positive_log
    assert "AUDITED_ACTUAL IndependentAuditFixture.localProof IndependentAuditFixture.localProof local" in positive_log
    negative_log = (out / "PrivateNegative.lean.log").read_text()
    assert "depends on sorry or unrecognized axioms" in negative_log and "IndependentAuditFixture.customAuditOnly" in negative_log
result = {"passed": True, "executed_utc": datetime.now(timezone.utc).isoformat(), "scope": "Auditor fixture only, not NLA proof-source acceptance", "driver_sha256": sha(BASE / "replay.py"), "checker_sha256": sha(Path(__file__)), "lean_sha256": sha(LEAN), "positive_private_local_public_passed": True, "custom_axiom_hidden_in_private_theorem_rejected": True, "negative_control_accepted_as_a_proof": False, "commands": commands, "proof_inputs_changed": False, "full_TR04_Target_proved": False}
p = out / "result.json"
p.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"passed": True, "result_sha256": sha(p), "negative_control": "correctly rejected"}, indent=2))
