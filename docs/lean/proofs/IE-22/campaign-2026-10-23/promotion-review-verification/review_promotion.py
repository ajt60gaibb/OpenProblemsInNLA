#!/usr/bin/env python3
"""Independent static review of IE22 promotion. Never executes Lean or claims new CI."""
import argparse, collections, datetime, gzip, hashlib, importlib.util, io, json, os, re, subprocess, sys, tarfile
from pathlib import Path, PurePosixPath
P=argparse.ArgumentParser();P.add_argument("--repo",type=Path,required=True);P.add_argument("--commit",required=True);P.add_argument("--snapshot",type=Path,required=True);P.add_argument("--output",type=Path,required=True);a=P.parse_args()
a.output.mkdir(parents=True,exist_ok=True);a.snapshot.mkdir(parents=True,exist_ok=False)
C=a.commit; OLD="06f31cdd4f76d90c7590b5582b8db4975a0055d8"; PROMO="6202e6668a889a0286120533f160ca61de4d0cf4"; BASE="01ed3c64648d2d8350ba80c4018894b6d785d2c9"; SRC="353ebcfcbbcfc08184c32f391ecb6068c7d9098f"
PKG="linear-systems-and-elimination/IE-22/lean"; DOC="docs/lean/proofs/IE-22/campaign-2026-10-23"; PAGE="linear-systems-and-elimination/IE-22/README.md"
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*v):return subprocess.check_output(["git","-C",str(a.repo),*v])
blob_cache={}
def blob(r,p):
    key=(r,p)
    if key not in blob_cache:blob_cache[key]=git("show",r+":"+p)
    return blob_cache[key]
def tree(r):return set(git("ls-tree","-r","--name-only",r).decode().splitlines())
paths=tree(C);registry=json.loads(blob(C,"problem_ids.json"));origlock=json.loads(blob(C,DOC+"/preproof/INPUT_LOCK.json"))
# Batch-read candidate Lean sources rather than spawn one process per import.
with tarfile.open(fileobj=io.BytesIO(git("archive","--format=tar",C,"*.lean")),mode="r:") as tf:
    for member in tf.getmembers():
        if member.isfile():blob_cache[C,member.name]=tf.extractfile(member).read()
selected={"AGENTS.md","problem_ids.json","README.md","CATALOG.md","RESOLVED.md","tools","tests","docs/lean","lean-statements","linear-systems-and-elimination/IE-22"}
selected.update(registry.values());selected.update(e["path"] for e in origlock["reviewed_inputs"])
for metadata_path in sorted(p for p in paths if p.startswith("docs/lean/statements/") and p.endswith("/statement.json")):
    for review in json.loads(blob(C,metadata_path)).get("reviews",[]):
        selected.update(review.get("input_sha256",{}))
        selected.add(review["report_path"])
# Inventory follows only the actual live Challenge/Solution import closures.
for readme in registry.values():
    project=str(PurePosixPath(readme).parent)+"/lean/"
    pending=[project+"Challenge.lean",project+"Solution.lean"];seen=set()
    while pending:
        rel=pending.pop()
        if rel in seen or rel not in paths:continue
        seen.add(rel);selected.add(rel)
        for line in blob(C,rel).decode().splitlines():
            if re.match(r"^\s*(?:public\s+)?import\s",line):
                mods=re.sub(r"^\s*(?:public\s+)?import\s+","",line).split("--",1)[0]
                for m in mods.split():
                    m=m.replace("«","").replace("»","")
                    if re.fullmatch(r"[\w.]+",m):pending.append(project+m.replace(".","/")+".lean")
archive=git("archive","--format=tar",C,*sorted(selected))
with tarfile.open(fileobj=io.BytesIO(archive),mode="r:") as tf:
    for m in tf.getmembers():
        p=PurePosixPath(m.name)
        if p.is_absolute() or ".." in p.parts or not(m.isfile() or m.isdir()):raise ValueError("unsafe archive member "+m.name)
        if m.isfile():
            dest=a.snapshot/m.name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(tf.extractfile(m).read())
# Read-only object access for existing preservation auditors. No git mutation is run here.
(a.snapshot/".git").write_text("gitdir: "+git("rev-parse","--absolute-git-dir").decode().strip()+"\n")
checks=[];commands=[]
def ck(n,v,**d):checks.append({"check":n,"pass":bool(v),**d})
def run(n,argv):
    env=os.environ.copy();env["PYTHONPATH"]="/private/tmp/nla-oct23-pydeps"+os.pathsep+str(a.snapshot/"tools")
    r=subprocess.run(argv,cwd=a.snapshot,env=env,capture_output=True,text=True)
    log=r.stdout+r.stderr;(a.output/(n+".log")).write_text(log)
    commands.append({"name":n,"argv":list(map(str,argv)),"exit_code":r.returncode,"log_sha256":sha(log.encode())})
    ck(n,r.returncode==0);print(n,r.returncode,flush=True);return log
lock=json.loads(blob(C,DOC+"/PROMOTION_INPUT_LOCK.json"));items=lock["package_inputs"]
ck("promotion_59_unique_inputs",len(items)==len({e["path"] for e in items})==59)
for e in items:
    b=blob(C,PKG+"/"+e["path"])
    ck("package_lock:"+e["path"],len(b)==e["bytes"] and sha(b)==e["sha256"] and b==blob(PROMO,PKG+"/"+e["path"]),sha256=sha(b),bytes=len(b))
leans=sorted(p for p in paths if p.startswith(PKG+"/") and p.endswith(".lean"))
ck("exact_27_Lean_files",len(leans)==27)
for p in leans:ck("accepted_Lean_identity:"+p,blob(C,p)==blob(OLD,p),sha256=sha(blob(C,p)))
ck("source_and_reviewed_23_exact",all(blob(C,PKG+"/"+str(p.relative_to(a.snapshot/PKG)))==blob(SRC,"lean-statements/"+str(p.relative_to(a.snapshot/PKG))) for root in ["NLA","Reviewed"] for p in (a.snapshot/PKG/root).rglob("*.lean")))
ck("all_217_permanent_IDs_unchanged",len(registry)==217 and all(json.loads(blob(r,"problem_ids.json"))==registry for r in [BASE,OLD,PROMO]))
readmes={i:blob(C,p).decode() for i,p in registry.items()}
counts=collections.Counter(re.search(r"(?m)^\*\*Status:\*\* ([^\n]+)",v).group(1).strip() for v in readmes.values())
ck("catalog_85_Lean_verified_33_Solved",counts["Lean verified"]==85 and counts["Solved"]==33,counts=dict(counts))
old=blob(OLD,PAGE).decode();new=blob(C,PAGE).decode()
before,tail=old.split("## Lean formalization scaffold\n",1);_,after=tail.split("## Problem statement\n",1)
normalized=new.replace("**Status:** Lean verified\n","**Status:** Solved\n",1).replace("**Last checked:** 2026-10-26\n","**Last checked:** 2026-09-11\n",1)
ck("exact_original_preamble_and_full_historical_suffix",normalized.startswith(before) and new.endswith("## Problem statement\n"+after))
ck("whole_original_readme_retained",blob(C,"linear-systems-and-elimination/IE-22/ORIGINAL.md")==blob("5487945e5a72abd952b0c89915915de8cc9b3e65",PAGE)==blob(C,"docs/lean/statements/IE-22/ORIGINAL.md"))
for name,original in {
"preproof-inventory.md":DOC+"/preproof/PRE_REVIEW_INVENTORY.md",
"preproof-verification.md":DOC+"/preproof/PRE_REVIEW_VERIFICATION.md",
"full-source-inventory.md":DOC+"/full-source-review-inventory/SOURCE_REVIEW_INVENTORY.md",
"full-source-verification.md":DOC+"/full-source-and-kernel-review-verification/REVIEW.md",
"package-inventory.md":DOC+"/package-review-inventory/PACKAGE_REVIEW_INVENTORY.md"}.items():
    actual=blob(C,PKG+"/reviews/"+name)
    if original not in paths:
        matches=[p for p in paths if p.startswith(DOC+"/") and p!=PKG+"/reviews/"+name and blob(C,p)==actual] if len(actual)<100000 else []
        ck("verbatim_copied_review:"+name,bool(matches),source_matches=matches)
    else:ck("verbatim_copied_review:"+name,actual==blob(C,original),source=original,sha256=sha(actual))
cfg=json.loads(blob(C,PKG+"/comparator.json"));meta=json.loads(blob(C,PKG+"/formalization.yaml"));names=["NLA.Proofs.IE22.uniform_squared_upper","NLA.Proofs.IE22.near_sharp_unit_row_witness","NLA.Proofs.IE22.target"];axioms=["propext","Classical.choice","Quot.sound"]
ck("exact_three_exports_standard_axioms_no_replaceable_definitions",cfg["theorem_names"]==names and cfg["definition_names"]==[] and cfg["permitted_axioms"]==axioms and [e["declaration"] for e in meta["status"]["main_results"]]==names)
ck("full_problem_promotion_and_honest_original_CI_scope",meta["status"]["phase"]=="complete" and meta["status"]["whole_problem_verified"] is True and meta["status"]["canonical_status"]=="Lean verified" and all("40255260833/job121355717650" in x["verification_status"] and "88b9366e6cfcef7e60a2d740ff8a7101399bf1a8" in x["verification_status"] and "54" in x["verification_status"] and "fresh committed-project CI" in x["verification_status"] for x in meta["status"]["main_results"]))
py=sys.executable
run("manifest",[py,a.snapshot/"tools/lean/validate_manifest.py",a.snapshot/PKG])
run("statement_guard",[py,a.snapshot/"tools/lean_statements/check.py","--root",a.snapshot,"validate"])
run("ID_guard",[py,a.snapshot/"tools/validate_problem_ids.py","--base-ref",BASE])
run("statement_inventory",[py,a.snapshot/"tools/statement_inventory.py","--root",a.snapshot,"--base-ref",BASE,"--check"])
run("inventory_regressions",[py,"-m","unittest","discover","-s",str(a.snapshot/"tests"),"-p","test_statement_inventory.py","-v"])
run("author_preservation_audit",[py,a.snapshot/DOC/"audit_package.py","--root",a.snapshot,"--output",a.output/"author-preservation-replay.json"])
spec=importlib.util.spec_from_file_location("reviewed_author_guard",a.snapshot/DOC/"audit_package.py");module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
cases={"original":(old,True),"authorized_promotion":(new,True),"target_mutation":(new.replace("For", "Wrong",1) if False else new.replace("## Problem statement\n","## Problem statement\nALTERED\n",1),False),"credit_mutation":(new.replace("Matthew J. Colbrook","Other Person"),False),"wrong_date":(new.replace("2026-10-26","2026-10-27"),False),"wrong_status":(new.replace("**Status:** Lean verified","**Status:** Open"),False),"historical_suffix_mutation":(new+"ALTERED\n",False)}
for n,(v,e) in cases.items():ck("README_guard_control:"+n,module.reviewed_readme_preserved(old,v)==e,expected=e)
# Revalidate retained original receipt offline, with original head/merge identity unchanged.
run("retained_original_Linux_receipt_offline",[py,a.snapshot/DOC/"linux-pr368-initial/audit_linux_ci.py","--repo",a.snapshot,"--output",a.output/"retained-Linux-replay"])
report={"reviewer":"/root/verification","scope":"Independent metadata/status/preservation review and offline replay of existing original Linux evidence; no new Lean, Comparator, CI or promotion-run acceptance claim","UTC":datetime.datetime.now(datetime.timezone.utc).isoformat(),"commit":C,"initial_accepted_head":OLD,"original_complete_source":SRC,"published_base":BASE,"passed":all(x["pass"] for x in checks),"checks":checks,"commands":commands,"snapshot":str(a.snapshot),"script_sha256":sha(Path(__file__).read_bytes())}
(a.output/"result.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps({"pass":report["passed"],"checks":len(checks),"failed":[x["check"] for x in checks if not x["pass"]]}))
sys.exit(0 if report["passed"] else 1)

