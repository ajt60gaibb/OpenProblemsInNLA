#!/usr/bin/env python3
"""Non-author immutable TR26 33-module isotropic-endpoint replay; no endpoint/CI claim."""
import argparse,datetime,hashlib,json,os,re,subprocess
from pathlib import Path
REF="4692336f0e1a50d5e261bba68277875da30fba51";BASE="5487945e5a72abd952b0c89915915de8cc9b3e65";PACKET="docs/lean/proofs/TR-26/campaign-2026-10-26/preproof/";DOC="docs/lean/proofs/TR-26/campaign-2026-10-26/";STANDARD={"propext","Classical.choice","Quot.sound"}
def sha(b):return hashlib.sha256(b).hexdigest()
def clean_lean(text):
    out=[];i=0;depth=0
    while i<len(text):
        if depth:
            if text.startswith("/-",i):depth+=1;out.extend("  ");i+=2
            elif text.startswith("-/",i):depth-=1;out.extend("  ");i+=2
            else:out.append("\n" if text[i]=="\n" else " ");i+=1
        elif text.startswith("/-",i):depth=1;out.extend("  ");i+=2
        elif text.startswith("--",i):
            j=text.find("\n",i);j=len(text) if j<0 else j;out.extend(" "*(j-i));i=j
        elif text[i]=='"':
            out.append(" ");i+=1
            while i<len(text):
                if text[i]=="\\":out.extend("  ");i+=2
                elif text[i]=='"':out.append(" ");i+=1;break
                else:out.append("\n" if text[i]=="\n" else " ");i+=1
        else:out.append(text[i]);i+=1
    assert depth==0
    return "".join(out)
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("--repo",type=Path,required=True);p.add_argument("--lean",type=Path,required=True);p.add_argument("--packages",type=Path,required=True);p.add_argument("--build",type=Path,required=True);p.add_argument("--output",type=Path,required=True);a=p.parse_args()
    a.output.mkdir(parents=True,exist_ok=True);assert not a.build.exists(),"Fresh owned build root required";a.build.mkdir(parents=True)
    src=a.build/"source";obj=a.build/"out";src.mkdir();obj.mkdir()
    for d in ["sources","logs","consumers"]:(a.output/d).mkdir(exist_ok=True)
    def git(*v):return subprocess.check_output(["git","-C",str(a.repo),*v])
    def blob(path,ref=REF):return git("show",ref+":"+path)
    checks=[]
    def ck(n,v,**d):checks.append({"check":n,"pass":bool(v),**d})
    receipt_bytes=blob(DOC+"ISOTROPIC_ENDPOINT_CHECKPOINT.json");receipt=json.loads(receipt_bytes)
    (a.output/"ISOTROPIC_ENDPOINT_CHECKPOINT.json").write_bytes(receipt_bytes)
    ck("exact_isotropic_only_scope",receipt["full_target_proved"] is False and receipt["Linux_CI_claimed"] is False and receipt["canonical_status"]=="Solved")
    files=git("ls-tree","-r","--name-only",REF,"--","lean-statements/NLA/Proofs/TR26").decode().splitlines()
    ck("exact_33_module_set",set(files)=={e["path"] for e in receipt["proof_inputs"]} and len(files)==33)
    ck("preproof_authorization_precedes_source",subprocess.run(["git","-C",str(a.repo),"merge-base","--is-ancestor",receipt["preproof_authorization_commit"],REF]).returncode==0)
    lock_bytes=blob(PACKET+"INPUT_LOCK.json");lock=json.loads(lock_bytes);originals=[]
    ck("exact_preapproved_input_lock",sha(lock_bytes)=="59314bd19a35f47dadd9a672517d4f9053682b4454b79c571cb915231342a91c")
    for e in lock["reviewed_inputs"]:
        b=blob(e["path"]);old=blob(e["path"],BASE);frozen=blob(PACKET+"frozen/"+e["path"])
        originals.append({"path":e["path"],"sha256":sha(b),"pass":b==old==frozen and sha(b)==e["sha256"] and len(b)==e["bytes"]})
    ck("all_24_original_statement_registry_manuscript_inputs_unchanged",len(originals)==24 and all(e["pass"] for e in originals))
    modules={};order=[]
    def imports(b):return re.findall(r"^import\s+([\w.]+)\s*$",b.decode(),re.M)
    def visit(name):
        if not name.startswith(("NLA.","Reviewed.")) or name in modules:return
        b=blob("lean-statements/"+name.replace(".","/")+".lean")
        for child in imports(b):visit(child)
        modules[name]=b;order.append(name)
    for f in files:visit(f[len("lean-statements/"):-5].replace("/","."))
    visit("Reviewed.TR26")
    ck("exact_36_module_own_closure",len(modules)==36 and len([n for n in modules if n.startswith("NLA.Proofs.TR26.")])==33)
    records=[];decls=[]
    for n,b in modules.items():
        rel=n.replace(".","/")+".lean"
        for root in [src,a.output/"sources"]:
            f=root/rel;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b)
        records.append({"module":n,"path":"lean-statements/"+rel,"sha256":sha(b),"bytes":len(b),"imports":imports(b)})
        if n.startswith("NLA.Proofs.TR26."):
            text=b.decode();code=clean_lean(text)
            ck("no_holes_custom_axioms_or_unsafe:"+n,not re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b",code) and 'set_option leancert.trust "kernel"' in text)
            namespace_stack=[]
            for line in code.splitlines():
                ns=re.match(r"^namespace\s+([\w.]+)\s*$",line)
                if ns:namespace_stack.append(ns[1]);continue
                if re.match(r"^end(?:\s+\S+)?\s*$",line):
                    if namespace_stack:namespace_stack.pop()
                    continue
                dec=re.match(r"^(?:@\[[^\n]*\]\s*)?(theorem|lemma|def|abbrev)\s+([^\s({:]+)",line)
                if dec:
                    kind,label=dec.groups();decls.append({"module":n,"name":".".join(namespace_stack+[label]),"kind":"theorem" if kind in ["theorem","lemma"] else "definition"})
    for e in receipt["proof_inputs"]:
        b=blob(e["path"]);ck("checkpoint_hash:"+e["path"],sha(b)==e["sha256"] and len(b)==e["bytes"],sha256=sha(b),bytes=len(b))
    author_bytes=blob(DOC+"support-02-author-acceptances.json");author=json.loads(author_bytes)+json.loads(blob(DOC+"isotropic-endpoint-author-acceptances.json"))
    (a.output/"support-author-acceptances.json").write_bytes(author_bytes)
    (a.output/"isotropic-author-acceptances.json").write_bytes(blob(DOC+"isotropic-endpoint-author-acceptances.json"))
    ck("33_retained_author_source_receipts_match_without_independent_claim",len(author)==33 and {e["module"] for e in author}=={r["module"] for r in records if r["module"].startswith("NLA.Proofs.TR26.")} and all(e["record"]["exit_code"]==0 and e["record"]["sha256"]==sha(modules[e["module"]]) for e in author))
    previous=json.loads(blob(DOC+"FOUNDATION_CHECKPOINT.json"))
    ck("six_previously_reviewed_foundations_byte_identical",len(previous["proof_inputs"])==6 and all(sha(blob(e["path"]))==e["sha256"] for e in previous["proof_inputs"]))
    prior=json.loads(blob(DOC+"SUPPORT_CHECKPOINT_02.json"))
    ck("all27_previously_reviewed_support_sources_byte_identical",len(prior["proof_inputs"])==27 and all(sha(blob(e["path"]))==e["sha256"] for e in prior["proof_inputs"]))
    ck("actual_endpoint_receipt_scope_exact",receipt["isotropic_endpoint"]["constant"]=="NLA.Proofs.TR26.isotropic_degree" and receipt["nonisotropic_endpoint_proved"] is False and receipt["isotropic_endpoint_author_kernel_checked"] is True)
    pins=[]
    manifest=json.loads(blob("lean-statements/lake-manifest.json"))
    def pincheck(dep):
        d=a.packages/dep["name"];head=subprocess.check_output(["git","-C",str(d),"rev-parse","HEAD"],text=True).strip();status=subprocess.check_output(["git","-C",str(d),"status","--porcelain","--untracked-files=no"],text=True)
        return {"name":dep["name"],"expected":dep["rev"],"actual":head,"tracked_clean":not status,"pass":head==dep["rev"] and not status}
    pins=[pincheck(dep) for dep in manifest["packages"]];ck("all_ten_read_only_dependency_pins",len(pins)==10 and all(e["pass"] for e in pins))
    version=subprocess.check_output([str(a.lean),"--version"],text=True).strip()
    ck("exact_Lean_4_33_1",blob("lean-statements/lean-toolchain")==b"leanprover/lean4:v4.33.1\n" and "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version)
    env=os.environ.copy();deps=sorted(d/".lake/build/lib/lean" for d in a.packages.iterdir() if (d/".lake/build/lib/lean").is_dir());env["LEAN_PATH"]=":".join(map(str,[obj]+deps+[a.lean.parent.parent/"lib/lean"]))
    commands=[]
    def run(name,b,expected=0):
        f=src/(name.replace(".","/")+".lean");f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b)
        target=obj/(name.replace(".","/")+".olean");target.parent.mkdir(parents=True,exist_ok=True)
        (a.output/"consumers"/(name+".lean.txt")).write_bytes(b)
        argv=[str(a.lean),"-R",str(src),"-o",str(target),str(f)]
        r=subprocess.run(argv,cwd=src,env=env,capture_output=True,text=True,timeout=360)
        log=r.stdout+r.stderr;(a.output/"logs"/(name+".log")).write_text(log)
        command={"module":name,"argv":argv,"exit_code":r.returncode,"expected_exit":expected,"source_sha256":sha(b),"log_sha256":sha(log.encode())};commands.append(command);print(name,r.returncode,flush=True)
        if r.returncode!=expected:
            (a.output/"failed-command.json").write_text(json.dumps(command,indent=2)+"\n");print(log,flush=True);raise RuntimeError("Unexpected result: "+name)
        return log
    for n in order:run(n,modules[n])
    guards='''open Lean Elab Command
elab "#review_theorem " target:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  match ← liftCoreM <| getConstInfo name with
  | .thmInfo _ => pure ()
  | _ => throwError "review requires an actual theorem: {name}"
elab "#review_definition " target:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  match ← liftCoreM <| getConstInfo name with
  | .defnInfo _ => pure ()
  | _ => throwError "review requires an actual definition: {name}"
elab "#review_absent " target:ident : command => do
  if (← getEnv).contains target.getId then
    throwError "support scope unexpectedly contains {target.getId}"
'''
    audit="\n".join("import "+n for n in order)+'\nset_option leancert.trust "kernel"\n'+guards
    audit+="\n".join("#review_"+d["kind"]+" "+d["name"]+"\n#assert_trust kernel "+d["name"]+"\n#print axioms "+d["name"] for d in decls)+"\n"
    audit+='''#review_absent NLA.Proofs.TR26.nonisotropic_degree
#review_theorem NLA.Proofs.TR26.isotropic_degree
#review_absent NLA.Proofs.TR26.target
example : NLA.Statements.TR26.Target = NLA.ReviewedStatements.TR26.Target := rfl
open NLA.Statements.TR26 NLA.Proofs.TR26 NLA.Proofs.TR26.BinaryDiscriminant
example (d : ℕ) (a b : ℂ) :
    binaryEval (binaryDenominator d) a b = denominator (veronese d a b) :=
  binaryDenominator_eval d a b
example {d : ℕ} (H : Parameter d) (a b : ℂ) :
    binaryEval (binaryNumerator H) a b = numerator H (veronese d a b) :=
  binaryNumerator_eval H a b
example (d : ℕ) (f : IncidenceRing d) :
    f ∈ openVanishingIdeal d ↔ VanishesOnOpen d f := mem_openVanishingIdeal_iff d f
example (d : ℕ) (z : CurveVector d) (H : Parameter d) :
    JacobianSpace d z H = idealConormal (Sum.inl : Index d → IncidenceVariable d)
      (incidenceCoordinates z H) (openVanishingIdeal d) := jacobianSpace_eq_conormal d z H
example {σ ι : Type} (index : ι → σ) (x : σ → ℂ) (S : Set (MvPolynomial σ ℂ))
    (hS : ∀ f ∈ S, MvPolynomial.eval x f = 0) :
    idealConormal index x (Ideal.span S) =
      Submodule.span ℂ (partialGradient index x '' S) := idealConormal_span index x S hS
example {k : ℕ} (hk : 2 ≤ k) :
    (fixedDiscriminant k).totalDegree = 2 * k - 2 := fixedDiscriminant_totalDegree hk
example {k : ℕ} (hk : 2 ≤ k) (c : Fin (k+1) → ℂ)
    (h : HasMultipleProjectiveRoot k c) :
    MvPolynomial.eval c (fixedDiscriminant k) = 0 := multiple_projective_root_vanishes hk c h
'''
    endpoint_header=blob(PACKET+"Challenge.lean").decode().split("theorem isotropic_degree",1)[1].split(":= by",1)[0]
    audit+="example"+endpoint_header+":= NLA.Proofs.TR26.isotropic_degree d hd\n"
    log=run("FoundationExactAudit",audit.encode());closures={}
    for n,v in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S):closures[n]=[x.strip() for x in v.split(",") if x.strip()]
    for n in re.findall(r"'([^']+)' does not depend on any axioms",log):closures[n]=[]
    ck("all_declaration_kinds_kernel_and_standard_axioms",set(closures)=={d["name"] for d in decls} and all(set(v)<=STANDARD for v in closures.values()),declarations=len(decls),closures=closures)
    ck("exact_support_consumers_and_literal_frozen_Target_identity",True,consumer_sha256=sha(audit.encode()))
    ck("literal_isotropic_endpoint_present_nonisotropic_and_full_Target_absent",True)
    challenge=blob(PACKET+"Challenge.lean");ck("exact_preapproved_Challenge",sha(challenge)=="122ad60aaddf59e91dacd627637cf7237b8614d83b6d2eead381a76a698d7aba")
    run("ReferenceHoles",challenge)
    neg='import ReferenceHoles\nset_option leancert.trust "kernel"\n'+"".join("#assert_trust kernel NLA.Proofs.TR26."+n+"\n" for n in ["nonisotropic_degree","isotropic_degree","target"])
    log=run("FoundationHoleRejection",neg.encode(),1);ck("all_three_actual_endpoint_holes_rejected",log.count("depends on sorry or unrecognized axioms")==3 and "sorryAx" in log)
    fake="import NLA.Statements.TR26\n"+guards+"def FoundationFakeTheorem : True := True.intro\n#review_theorem FoundationFakeTheorem\n"
    log=run("FoundationKindRejection",fake.encode(),1);ck("proof_valued_definition_rejected_as_theorem","review requires an actual theorem" in log)
    tainted='import NLA.Statements.TR26\nset_option leancert.trust "kernel"\naxiom FoundationCustomAxiom : True\ntheorem FoundationTainted : True := FoundationCustomAxiom\n#assert_trust kernel FoundationTainted\n'
    log=run("FoundationCustomAxiomRejection",tainted.encode(),1);ck("actual_custom_axiom_rejected","FoundationCustomAxiom" in log and "depends on sorry or unrecognized axioms" in log)
    postpins=[pincheck(dep) for dep in manifest["packages"]];ck("all_dependency_pins_remain_clean_after_build",all(e["pass"] for e in postpins))
    ck("all_private_source_bytes_remain_exact",all((src/(n.replace(".","/")+".lean")).read_bytes()==b for n,b in modules.items()))
    ck("private_objects_first_no_mutable_project_imports",env["LEAN_PATH"].split(":")[0]==str(obj) and all(str(d).startswith(str(a.packages)+"/") for d in deps))
    report={"reviewer":"/root/verification","UTC":datetime.datetime.now(datetime.timezone.utc).isoformat(),"checkpoint_commit":REF,"scope":"Literal isotropic reduced-degree endpoint at immutable33module checkpoint; no nonisotropic endpoint, full Target or Linux CI","passed":all(c["pass"] for c in checks),"checks":checks,"source_records":records,"declarations":decls,"dependency_pins":pins,"original_inputs":originals,"compiler_version":version,"compiler_sha256":sha(a.lean.read_bytes()),"private_build":str(a.build),"LEAN_PATH":env["LEAN_PATH"],"commands":commands,"full_Target_proved":False,"Linux_CI_run":False,"script_sha256":sha(Path(__file__).read_bytes())}
    (a.output/"result.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"passed":report["passed"],"checks":len(checks),"source_modules":len(modules),"support_modules":33,"declarations":len(decls),"theorems":sum(d["kind"]=="theorem" for d in decls),"commands":len(commands),"failed":[c["check"] for c in checks if not c["pass"]]}))
    return 0 if report["passed"] else 1
if __name__=="__main__":raise SystemExit(main())

