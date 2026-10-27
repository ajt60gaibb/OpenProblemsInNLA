#!/usr/bin/env python3
"""Independent input/pin validation for TR26 draft; no target proof."""
import argparse, datetime, hashlib, json, subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument("--repo",type=Path,required=True);p.add_argument("--packet",type=Path,required=True);p.add_argument("--packages",type=Path,required=True);p.add_argument("--output",type=Path,required=True);a=p.parse_args()
COMMIT="94dd4adb910c5b5e1114528c1c4d9f272347743a";PREFIX="docs/lean/proofs/TR-26/campaign-2026-10-26/preproof/"
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(["git","-C",str(a.repo),*args])
def blob(r,n):return git("show",r+":"+n)
checks=[]
def ck(n,v,**d):checks.append({"check":n,"pass":bool(v),**d})
b=(a.packet/"INPUT_LOCK.json").read_bytes();lock=json.loads(b)
ck("approved_lock_hash",sha(b)=="59314bd19a35f47dadd9a672517d4f9053682b4454b79c571cb915231342a91c" and b==blob(COMMIT,PREFIX+"INPUT_LOCK.json"),sha256=sha(b))
ck("exact_24_unique_inputs",len(lock["reviewed_inputs"])==len({e["path"] for e in lock["reviewed_inputs"]})==24)
for e in lock["reviewed_inputs"]:
    n=e["path"];data=(a.packet/"frozen"/n).read_bytes()
    ck("original_input:"+n,len(data)==e["bytes"] and sha(data)==e["sha256"] and data==blob(COMMIT,PREFIX+"frozen/"+n) and all(data==blob(r,n) for r in [lock["published_base"],lock["latest_published_base_checked"],COMMIT]),sha256=sha(data),bytes=len(data))
for n,h in lock["contract_and_scaffold_inputs"].items():
    data=(a.packet/n).read_bytes();ck("contract_input:"+n,sha(data)==h and data==blob(COMMIT,PREFIX+n),sha256=sha(data))
registry=json.loads((a.packet/"frozen/problem_ids.json").read_bytes())
ck("217_IDs_and_TR26_path",len(registry)==217 and registry["TR-26"]=="tensor-computations/TR-26/README.md")
live=(a.packet/"frozen/lean-statements/NLA/Statements/TR26.lean").read_text();reviewed=(a.packet/"frozen/lean-statements/Reviewed/TR26.lean").read_text()
ck("frozen_namespace_only_copy",reviewed[reviewed.index("import "):].replace("NLA.ReviewedStatements.TR26","NLA.Statements.TR26")==live)
manifest=json.loads((a.packet/"frozen/lean-statements/lake-manifest.json").read_bytes())
ck("ten_pinned_dependencies",len(manifest["packages"])==10)
for dep in manifest["packages"]:
    d=a.packages/dep["name"]
    head=subprocess.check_output(["git","-C",str(d),"rev-parse","HEAD"],text=True).strip()
    status=subprocess.check_output(["git","-C",str(d),"status","--porcelain","--untracked-files=no"],text=True)
    ck("read_only_dependency:"+dep["name"],head==dep["rev"] and not status,expected=dep["rev"],actual=head,tracked_status=status)
res=json.loads((a.output/"result.json").read_bytes())
ck("six_fresh_compiler_commands_pass_expected_status",res["passed"] and len(res["records"])==6 and [e["exit_code"] for e in res["records"]]==[0,0,0,0,0,1] and "4.33.1" in res["Lean_version"] and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in res["Lean_version"])
for record in res["records"]:
    log=(a.output/(record["module"]+".log")).read_bytes()
    ck("compiler_log:"+record["module"],sha(log)==record["log_sha256"])
ck("actual_three_holes_rejected",res["all_three_reference_holes_rejected"] and (a.output/"PlaceholderRejection.log").read_text().count("depends on sorry or unrecognized axioms")==3 and "sorryAx" in (a.output/"PlaceholderRejection.log").read_text())
report={"reviewer":"/root/verification","scope":"Independent immutable input validation, ten dependency pins, fresh statement-boundary replay and actual reference-hole rejection; no TR26 target proved","UTC":datetime.datetime.now(datetime.timezone.utc).isoformat(),"immutable_packet_commit":COMMIT,"lock_sha256":sha(b),"passed":all(c["pass"] for c in checks),"checks":checks,"compiler_result_sha256":sha((a.output/"result.json").read_bytes()),"script_sha256":sha(Path(__file__).read_bytes())}
(a.output/"INPUT_AND_PIN_AUDIT.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps({"pass":report["passed"],"checks":len(checks),"failed":[c["check"] for c in checks if not c["pass"]]}))
raise SystemExit(0 if report["passed"] else 1)

