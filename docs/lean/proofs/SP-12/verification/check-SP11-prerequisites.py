#!/usr/bin/env python3
"""Bind this frozen SP12 support snapshot to the actual Linux-checked SP11 code."""
import hashlib
import json
from pathlib import Path
import subprocess

REPO = Path(__file__).resolve().parents[5]
SOURCE = Path(__file__).with_name("support-review") / "source"
REF = "9264361fafb89b37b5c48236afebb304bc84110a"
records = []
for file in sorted(SOURCE.rglob("*.lean.txt")):
    name = str(file.relative_to(SOURCE))[:-4]
    if "/Proofs/SP11/" not in name and name not in ["NLA/Statements/SP11.lean", "NLA/Statements/Infrastructure.lean"]:
        continue
    checked = subprocess.check_output(["git", "show", REF + ":eigenvalues-and-inverse-problems/SP-11/lean/" + name], cwd=REPO)
    frozen = file.read_bytes()
    current = (REPO / "lean-statements" / name).read_bytes()
    records.append({"source": name, "sha256": hashlib.sha256(frozen).hexdigest(),
                    "matches_actual_checked_SP11_commit": frozen == checked,
                    "current_source_unchanged": current == frozen})
result = {"reference_commit": REF,
          "scope": "SP11 prerequisites in this actual SP12 support import closure match the canonical source bytes accepted by the complete SP11 Linux run",
          "records": records,
          "passed": len(records) == 38 and all(r["matches_actual_checked_SP11_commit"] and r["current_source_unchanged"] for r in records)}
Path(__file__).with_name("SP11-prerequisite-identity.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"passed": result["passed"], "SP11_prerequisite_sources": len(records)}))
raise SystemExit(0 if result["passed"] else 1)
