#!/usr/bin/env python3
"""Archive actual successful PF03 local commands and authenticated reuse origins.

This is a receipt audit, not a new Lean/Comparator invocation.
The complete original mixed-run receipts are retained losslessly as gzip.
"""
from pathlib import Path
import datetime
import gzip
import hashlib
import json
import re
import shutil

D = Path(__file__).resolve().parents[1]
L = D / "local-lean"
P = D / "publication/PF03/nonnegative-and-positive-factorizations/PF-03/lean"
OUT = P / "verification/local-2026-09-19"
OUT.mkdir(parents=True, exist_ok=True)


def sha(data):
    return hashlib.sha256(data).hexdigest()


receipts = {}


def read_receipt(path, expected=None):
    path = Path(path)
    raw = path.read_bytes()
    digest = sha(raw)
    if expected is not None:
        assert digest == expected, (path, digest, expected)
    obj = json.loads(raw)
    assert obj.get("end"), (path, "unfinished receipt")
    receipts[path.parent.name] = (raw, digest)
    return obj


top_path = L / "runs/recovery-047/RECEIPT.json"
top = read_receipt(top_path)
commands = [c for c in top["commands"]
            if c["module"].startswith("NLA.PF03.") or c["module"] == "Solution"]
assert len(commands) == 60
outputs = {c["module"]: c["output_sha256"] for c in commands}
records = []

for initial in commands:
    module = initial["module"]
    rel = module.replace(".", "/") + ".lean"
    source_hash = sha((P / rel).read_bytes())
    assert source_hash == initial["source_sha256"]
    actual_olean = L / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
    assert sha(actual_olean.read_bytes()) == initial["output_sha256"]
    c, run, chain = initial, "recovery-047", []
    seen = set()
    while c.get("status") == "reused_exact_successful_local_output":
        assert run not in seen, (module, "reuse cycle")
        seen.add(run)
        for name, digest in c["transitive_source_hashes"].items():
            assert sha((P / name).read_bytes()) == digest, (module, name)
        previous = Path(c["prior_receipt"])
        prior = read_receipt(previous, c["prior_receipt_sha256"])
        chain.append({"run": run, "prior": previous.parent.name,
                      "prior_receipt_sha256": c["prior_receipt_sha256"]})
        matches = [x for x in prior["commands"] if x["module"] == module]
        assert len(matches) == 1
        c, run = matches[0], previous.parent.name
        assert c["source_sha256"] == source_hash
        assert c["output_sha256"] == initial["output_sha256"]
    assert c["exit_code"] == 0, (module, run)
    assert "--threads=1" in c["argv"] and "--memory=4096" in c["argv"]
    for dep, digest in c.get("dependency_olean_sha256", {}).items():
        assert outputs[dep] == digest, (module, dep, "dependency output mismatch")
    log_path = L / "runs" / run / (module + ".log")
    raw_log = log_path.read_bytes()
    assert sha(raw_log) == c["log_sha256"]
    dest_log = OUT / "logs" / run / log_path.name
    dest_log.parent.mkdir(parents=True, exist_ok=True)
    dest_log.write_bytes(raw_log)
    records.append({"module": module, "source": rel, "source_sha256": source_hash,
                    "output_sha256": initial["output_sha256"], "reuse_chain": chain,
                    "fresh_success_run": run, "actual_fresh_command": c,
                    "log": str(dest_log.relative_to(OUT))})

axiom_log = (L / "runs/recovery-047/Solution.log").read_text()
axioms = {name: values.split(", ") if values else []
          for name, values in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", axiom_log)}
targets = json.loads((P / "comparator.json").read_text())["theorem_names"]
assert set(axioms) == set(targets) and len(axioms) == 25
allowed = {"propext", "Classical.choice", "Quot.sound"}
assert all(set(a) <= allowed for a in axioms.values())
(OUT / "actual-axioms.json").write_text(json.dumps(axioms, indent=2) + "\n")

receipt_index = {}
for run, (raw, digest) in sorted(receipts.items()):
    dest = OUT / "receipts" / (run + ".RECEIPT.json.gz")
    dest.parent.mkdir(parents=True, exist_ok=True)
    compressed = gzip.compress(raw, mtime=0)
    dest.write_bytes(compressed)
    receipt_index[run] = {"file": str(dest.relative_to(OUT)),
                          "original_sha256": digest, "gzip_sha256": sha(compressed)}

for name in ["serial_compile_recovery.py", "LOCAL-ENVIRONMENT.json"]:
    shutil.copy2(L / name, OUT / name)
audit = {
    "time": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "scope": "Actual macOS PF03 local compiler outputs and recursively checked reuse origins only",
    "new_Lean_run_by_archiver": False,
    "standalone_lake_build": "NOT_RUN; serial direct compiler commands are recorded verbatim",
    "GitHub_Comparator": "NOT_RUN_FOR_PF03",
    "aggregate_run": "recovery-047",
    "aggregate_receipt_sha256": sha(top_path.read_bytes()),
    "aggregate_command": next(c for c in commands if c["module"] == "Solution"),
    "fresh_aggregate_and_reused_module_count": len(commands),
    "kernel_trust_assertions_and_actual_axiom_reports": len(axioms),
    "compiler_sha256": top["compiler_sha256"],
    "runner_sha256": top["runner_sha256"],
    "resource_limits": {"compiler_processes": 1, "threads": 1, "memory_MiB": 4096},
    "module_records": records,
    "lossless_original_receipts": receipt_index,
    "mixed_run_warning": "Original receipts may include other problems and failures. Only the listed PF03 successful module commands support this audit.",
    "count_increment": 0,
}
(OUT / "LOCAL-REPLAY-AUDIT.json").write_text(json.dumps(audit, indent=2) + "\n")
print(json.dumps({"modules": len(records), "actual_axiom_reports": len(axioms),
                  "receipts": len(receipts), "audit_sha256": sha((OUT / "LOCAL-REPLAY-AUDIT.json").read_bytes()),
                  "scope": audit["scope"]}, indent=2))
