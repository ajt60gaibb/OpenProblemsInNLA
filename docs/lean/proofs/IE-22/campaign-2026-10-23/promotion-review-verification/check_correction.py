#!/usr/bin/env python3
"""Read-only binding of the final two-file coverage-count correction."""
import argparse, hashlib, json, subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument("--repo",type=Path,required=True);p.add_argument("--output",type=Path,required=True);a=p.parse_args()
OLD="799077c8d8b10bd9e266185a9ecc0c4c06abccd3";NEW="53ddb09ee25f863f483a05f91b3f02ff1ad7b0d6";PKG="linear-systems-and-elimination/IE-22/lean/";DOC="docs/lean/proofs/IE-22/campaign-2026-10-23/"
def git(*v):return subprocess.check_output(["git","-C",str(a.repo),*v])
def blob(c,p):return git("show",c+":"+p)
def sha(b):return hashlib.sha256(b).hexdigest()
checks=[]
def ck(n,v,**d):checks.append({"check":n,"pass":bool(v),**d})
names=git("diff","--name-only",OLD,NEW).decode().splitlines()
ck("exact_two_file_delta",set(names)=={"tools/statement_inventory.py","docs/lean/statements/COVERAGE.md"},paths=names)
ck("derived_scope_gap_count",b"{len(SCOPE_GAPS)} existing scope gaps" in blob(NEW,"tools/statement_inventory.py") and b"The 5 existing scope gaps remain explicit" in blob(NEW,"docs/lean/statements/COVERAGE.md"))
lock=json.loads(blob(NEW,DOC+"PROMOTION_INPUT_LOCK.json"))
ck("all_59_canonical_inputs_identical_to_executed_799_head",len(lock["package_inputs"])==59 and all(blob(OLD,PKG+e["path"])==blob(NEW,PKG+e["path"]) for e in lock["package_inputs"]))
ck("original_accepted_Linux_receipt_unchanged",all(blob(NEW,DOC+n)==blob(OLD,DOC+n) for n in ["LINUX_CI_RECEIPT.md","linux-pr368-initial/INVENTORY_REVIEW.md","linux-pr368-initial/INVENTORY_REVIEW.json"]))
for path in ["README.md","CATALOG.md"]:
    data=blob(NEW,path)
    ck("catalog_counts:"+path,b"33 solved (published or independently audited); 85 solved with Lean verification." in data)
rows=[line for line in blob(NEW,"CATALOG.md").decode().splitlines() if "/IE-22/README.md)" in line]
ck("unique_unchanged_IE22_catalog_ID_with_promoted_status",len(rows)==1 and "LEAN VERIFIED" in rows[0],row=rows)
diff=git("diff",OLD,NEW)
report={"scope":"Final two-file descriptive coverage correction only; no new execution evidence","old_head":OLD,"reviewed_head":NEW,"passed":all(c["pass"] for c in checks),"checks":checks,"diff_sha256":sha(diff),"script_sha256":sha(Path(__file__).read_bytes())}
a.output.write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps({"pass":report["passed"],"checks":len(checks)}));raise SystemExit(0 if report["passed"] else 1)

