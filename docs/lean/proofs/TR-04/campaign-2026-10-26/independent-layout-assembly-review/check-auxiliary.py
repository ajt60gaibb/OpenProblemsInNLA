#!/usr/bin/env python3
"""Read-only replay of the exact frozen generator and auxiliary hash checks."""
from pathlib import Path
import hashlib, json, subprocess

BASE = Path(__file__).resolve().parent
REPO = BASE.parents[5]
aux = json.loads((BASE / "auxiliary-input-check.json").read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert aux["passed"] and aux["generator_check"]["exit_code"] == 0
for v in aux["support_inputs"] + aux["author_results"] + [aux["retained_layout_superseded_lock"], aux["retained_layout_initial_diagnostic"]]:
    p = REPO / v["path"]
    assert p.is_file() and not p.is_symlink() and sha(p) == v["sha256"]
assert aux["retained_layout_superseded_lock"]["accepted_as_final"] is False
assert aux["retained_layout_initial_diagnostic"]["accepted_as_final"] is False
generator = REPO / aux["support_inputs"][0]["path"]
r = subprocess.run(["python3", str(generator), "--check"], cwd=REPO, capture_output=True, text=True)
assert r.returncode == 0, r.stdout + r.stderr
assert sha(BASE / "generator-check.log") == aux["generator_check"]["log_sha256"]
assert hashlib.sha256((r.stdout + r.stderr).encode()).hexdigest() == aux["generator_check"]["log_sha256"]
print(json.dumps({"passed": True, "scope": "Read-only auxiliary integrity and exact generator reproduction", "proof_inputs_changed": False, "full_TR04_Target_proved": False}, indent=2))
