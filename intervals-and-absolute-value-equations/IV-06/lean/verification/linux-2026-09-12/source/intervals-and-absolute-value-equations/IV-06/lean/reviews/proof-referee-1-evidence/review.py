"""Independent IV06 final referee 1: fresh proof, signature and trust audit.
Reviewer /root/leancert_examples authored neither IV06 statements nor proof.
Pinned MI22 dependency cache is read only; old project artifacts are excluded.
"""
from pathlib import Path
import datetime,hashlib,json,os,platform,re,subprocess,tempfile,time
OUT=Path(__file__).resolve().parent
P=OUT.parents[1]
REPO=P.parents[2]
D=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
B=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
save=lambda name,data:(OUT/name).write_text(json.dumps(data,indent=2)+'\n')
FREEZE='5bc8cfd590e82a27807ad5f6832c0cc5d634832979241f80eb30d8d76eaaa673'
COMPLETION='70aa87f73733ca81dfde6672b4ca09aab90243b3e00111a2cdb20db6f2568a77'
assert sha(P/'verification/proof-freeze.json')==FREEZE
assert sha(P/'reviews/proof-completion.md')==COMPLETION
f=json.loads((P/'verification/proof-freeze.json').read_text())

def integrity():
    for rel,entry in f['files'].items():
        assert sha(P/rel)==entry['sha256'] and (P/rel).stat().st_size==entry['bytes'],rel
    sources={}
    for rel,digest in f['source_files'].items():
        raw=subprocess.check_output(['git','show',f['source_commit']+':'+rel],cwd=REPO)
        assert hashlib.sha256(raw).hexdigest()==digest and (REPO/rel).read_bytes()==raw,rel
        sources[rel]={'sha256':digest,'git_blob':subprocess.check_output(['git','rev-parse',f['source_commit']+':'+rel],cwd=REPO,text=True).strip()}
    st=json.loads((P/'reviews/statement-freeze.json').read_text())
    for rel,digest in st['files'].items():
        if isinstance(digest,dict):digest=digest['sha256']
        assert sha(P/rel)==digest,rel
    assert len(f['files'])==126 and len(sources)==8 and len(st['files'])==32
    assert sha(P/'verification/proof-start.json')=='c4769fd9d06b5e17589a223bad83e80ce60b8c6d5f05615e5059457adf2a38e9'
    for rel,digest in f['statement_approvals'].items():assert sha(P/rel)==digest
    return {'status':'PASS','freeze_sha256':FREEZE,'completion_sha256':COMPLETION,
     'project_inputs':f['files'],'source_inputs':sources,'statement_input_count':32,
     'statement_approvals':f['statement_approvals'],'proof_start_sha256':sha(P/'verification/proof-start.json')}
before=integrity();save('integrity-before.json',before)

def signatures(text):
    return {n:' '.join(s.split()) for n,s in re.findall(r'^theorem\s+(\w+)\s+(.*?)\s*:=\s*by',text,re.S|re.M)}
ch=signatures((P/'Challenge.lean').read_text());sol=signatures((P/'Solution.lean').read_text())
cfg=json.loads((P/'comparator.json').read_text())
assert len(ch)==len(sol)==8 and ch==sol
assert cfg['theorem_names']==['NLA.IV06.'+n for n in sol]
assert cfg['definition_names']==[]
assert set(cfg['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
save('source-signatures.json',{'status':'PASS','count':8,'signatures':sol,
     'scope':'Exact normalized source signatures plus fresh Lean checking; not actual Linux Comparator.'})
modules=['NLA/IV06/Definitions.lean','NLA/IV06/Proof.lean','Solution.lean']
for rel in modules:
    text=(P/rel).read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',text),rel
    assert not re.search(r'^import\s+Challenge\b',text,re.M),rel
pins=[]
for pkg in json.loads((P/'lake-manifest.json').read_text())['packages']:
    path=D/pkg['name']
    rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=path,text=True).strip()
    dirty=subprocess.check_output(['git','status','--porcelain'],cwd=path,text=True)
    assert rev==pkg['rev'] and not dirty,(pkg['name'],rev,dirty)
    pins.append({'name':pkg['name'],'path':str(path),'revision':rev,'git_status_porcelain':dirty})
assert len(pins)==10;save('dependency-pins.json',pins)
(P/'.verification').mkdir(exist_ok=True)
prefix=Path(tempfile.mkdtemp(prefix='iv06-final-referee1-',dir=P/'.verification'))
paths=[str(prefix)]+[str(D/x['name']/'.lake/build/lib/lean') for x in reversed(pins)]+[str(B.parent/'lib/lean')]
env=dict(os.environ,LEAN_PATH=os.pathsep.join(paths))
record={'status':'RUNNING','reviewer':'/root/leancert_examples','independent':True,
 'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'platform':platform.platform(),
 'lean_version':subprocess.check_output([str(B/'lean'),'--version'],text=True).strip(),
 'dependency_root':str(D),'read_only_dependency_objects_reused':True,'dependency_source_rebuild':False,
 'old_project_objects_excluded':True,'fresh_prefix':str(prefix),'LEAN_PATH':env['LEAN_PATH'],
 'local_Lake_invocation':False,'Linux_Comparator_run':False,'commands':[]}
for rel in modules+['Challenge.lean','reviews/proof-referee-1-evidence/Inspect.lean']:
    cmd=[str(B/'lean')];objects=[]
    if not rel.endswith('/Inspect.lean'):
        for flag,suffix in [('-o','.olean'),('-i','.ilean')]:
            dest=prefix/Path(rel).with_suffix(suffix);dest.parent.mkdir(parents=True,exist_ok=True)
            cmd.extend([flag,str(dest)]);objects.append(dest)
    cmd.append(rel);label=rel.removesuffix('.lean').replace('/','-')
    print('Independent fresh check',rel,flush=True);t=time.monotonic()
    cp=subprocess.run(cmd,cwd=P,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=OUT/(label+'.log');log.write_bytes(cp.stdout)
    record['commands'].append({'source':rel,'source_sha256':sha(P/rel),'command':cmd,
     'exit_code':cp.returncode,'elapsed_seconds':time.monotonic()-t,'log':log.name,
     'log_sha256':sha(log),'fresh_objects':{str(x.relative_to(prefix)):sha(x) for x in objects if x.exists()}})
    save('fresh-checks.json',record);print('Exit',cp.returncode,flush=True)
    assert cp.returncode==0,cp.stdout.decode()
    holes=8 if rel=='Challenge.lean' else 0
    assert cp.stdout.count(b'warning:')==holes,cp.stdout.decode()
    assert cp.stdout.count(b'declaration uses `sorry`')==holes,cp.stdout.decode()
    assert b'error:' not in cp.stdout
reports=[]
for name in ['NLA-IV06-Proof.log','Solution.log']:
    for decl,body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(OUT/name).read_text()):
        axioms=[re.sub(r'\.\{[^}]*\}','',x.strip()) for x in body.split(',') if x.strip()]
        assert set(axioms)=={'propext','Classical.choice','Quot.sound'},(decl,axioms)
        reports.append({'name':decl,'axioms':axioms,'log':name})
assert len(reports)==17
save('axioms.json',{'count':17,'standard_three_only':True,'reports':reports})
raw=(OUT/'reviews-proof-referee-1-evidence-Inspect.log').read_text()
required=re.findall(r'^REFEREE_RETAINED: (\S+)',raw,re.M)
count=int(re.search(r'^REFEREE_PROJECT_DECLARATIONS: (\d+)',raw,re.M).group(1))
assert len(required)==23 and count==58,(len(required),count)
save('actual-dependencies.json',{'reached_project_declarations':count,'required_count':len(required),'actual_consumed':required})
after=integrity();save('integrity-after.json',after);assert before==after
record.update(status='PASS',fresh_commands=5,exact_exports=8,axiom_audits=17,
              required_dependencies=len(required),project_declarations=count,frozen_inputs_unchanged=True)
save('fresh-checks.json',record)
print(json.dumps({'status':'PASS','fresh_commands':5,'standard_three_audits':17,
 'exports':8,'project_declarations':count,'required_dependencies':len(required),'pins':10}),flush=True)
