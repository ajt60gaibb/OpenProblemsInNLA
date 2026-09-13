"""Independent final referee 2: MI03 integrity, fresh elaboration and trust.
Reviewer /root/leancert_examples; neither statement nor proof implementer.
Fresh-prefix orchestration is adapted from this reviewer's earlier MI03
statement audit and the shared campaign drivers. Candidate files are read-only.
"""
from pathlib import Path
import datetime,hashlib,json,os,platform,re,subprocess,tempfile,time

OUT=Path(__file__).resolve().parent
PROJECT=OUT.parents[1]
REPO=PROJECT.parents[2]
BIN=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin')
EXPECTED_FREEZE='fcff9e256a6425853b15def24260b419613a72d9122c0a5bedea4b4cd5f0fd1d'
EXPECTED_COMPLETION='919751e1f0595efd095250f2a6b2690b3214c96d988665fb7404d30690f2a729'
sha=lambda path:hashlib.sha256(Path(path).read_bytes()).hexdigest()
def save(name,obj):(OUT/name).write_text(json.dumps(obj,indent=2)+'\n')
def capture(argv,cwd=PROJECT):return subprocess.check_output(argv,cwd=cwd,text=True).strip()

def integrity():
    assert sha(PROJECT/'reviews/proof-freeze.json')==EXPECTED_FREEZE
    assert sha(PROJECT/'reviews/proof-completion.md')==EXPECTED_COMPLETION
    f=json.loads((PROJECT/'reviews/proof-freeze.json').read_text())
    current={}
    for name,entry in f['files'].items():
        p=PROJECT/name
        assert sha(p)==entry['sha256'] and p.stat().st_size==entry['bytes'],name
        current[name]=sha(p)
    sources={}
    for name,digest in f['source_files'].items():
        raw=subprocess.check_output(['git','show',f['source_commit']+':'+name],cwd=REPO)
        assert (REPO/name).read_bytes()==raw and hashlib.sha256(raw).hexdigest()==digest,name
        sources[name]={'sha256':digest,'git_blob':capture(['git','rev-parse',f['source_commit']+':'+name],REPO)}
    statement=json.loads((PROJECT/'reviews/statement-freeze.json').read_text())
    for name,digest in statement['files'].items():assert sha(PROJECT/name)==digest,name
    start=json.loads((PROJECT/'verification/proof-start.json').read_text())
    assert start['proof_and_solution_absent'] and start['files_verified']==27
    for name,digest in start['reports'].items():assert sha(PROJECT/name)==digest,name
    assert len(current)==101 and len(sources)==8 and len(statement['files'])==27
    return {'status':'PASS','proof_freeze_sha256':EXPECTED_FREEZE,
            'project_files':current,'source_files':sources,'statement_file_count':27,
            'both_statement_approvals_bound':start['reports'],
            'proof_start_record_sha256':sha(PROJECT/'verification/proof-start.json')}
before=integrity();save('integrity-before.json',before)
pins=[]
for package in json.loads((PROJECT/'lake-manifest.json').read_text())['packages']:
    path=PROJECT/'.lake/packages'/package['name']
    rev=capture(['git','rev-parse','HEAD'],path)
    dirty=capture(['git','status','--porcelain'],path)
    assert rev==package['rev'] and not dirty,(package['name'],rev,dirty)
    pins.append({'name':package['name'],'path':str(path),'rev':rev,'git_status_porcelain':dirty})
assert len(pins)==10;save('dependency-pins.json',pins)

def signatures(text):
    return {n:' '.join(s.split()) for n,s in re.findall(r'theorem\s+(\w+)\s+(.*?)\s*:=\s*by',text,re.S)}
challenge=signatures((PROJECT/'Challenge.lean').read_text())
solution=signatures((PROJECT/'Solution.lean').read_text())
config=json.loads((PROJECT/'comparator.json').read_text())
assert len(challenge)==len(solution)==8 and challenge==solution
assert set(config['theorem_names'])=={'NLA.MI03.'+n for n in solution}
assert config['definition_names']==[]
assert set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
save('source-signatures.json',{'status':'PASS','count':8,'signatures':solution,
      'scope':'Exact normalized source signatures plus fresh elaboration; actual Linux Comparator remains separate'})
modules=['NLA/MI03/Definitions.lean','NLA/MI03/Modulus.lean',
         'NLA/MI03/UpperBound.lean','NLA/MI03/Roots.lean',
         'NLA/MI03/Witness.lean','NLA/MI03/Sharpness.lean',
         'NLA/MI03/Proof.lean','Solution.lean']
for rel in modules:
    text=(PROJECT/rel).read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',text),rel
    assert not re.search(r'^import\s+Challenge\b',text,re.M),rel

(PROJECT/'.verification').mkdir(exist_ok=True)
prefix=Path(tempfile.mkdtemp(prefix='mi03-final-referee2-',dir=PROJECT/'.verification'))
oldpath=capture([str(BIN/'lake'),'env','printenv','LEAN_PATH']).split(os.pathsep)
old=(PROJECT/'.lake/build/lib/lean').resolve()
parts=[p for p in oldpath if Path(p).resolve()!=old]
assert len(parts)+1==len(oldpath)
env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(prefix)]+parts))
record={'reviewer':'/root/leancert_examples','independent':True,
 'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'platform':platform.platform(),'lean_version':capture([str(BIN/'lean'),'--version']),
 'fresh_prefix':str(prefix),'LEAN_PATH':env['LEAN_PATH'],'old_project_path_excluded':str(old),
 'pinned_dependency_objects_reused':True,'dependency_source_full_rebuild':False,
 'Linux_Comparator':False,'commands':[]}
for rel in modules+['Challenge.lean','reviews/proof-referee-2-evidence/Inspect.lean']:
    label=rel.removesuffix('.lean').replace('/','-')
    cmd=[str(BIN/'lean')]
    outputs=[]
    if not rel.endswith('/Inspect.lean'):
        for flag,ext in [('-o','.olean'),('-i','.ilean')]:
            dest=prefix/Path(rel).with_suffix(ext);dest.parent.mkdir(parents=True,exist_ok=True)
            cmd += [flag,str(dest)];outputs.append(dest)
    cmd.append(rel)
    print('Checking',rel,flush=True);start=time.monotonic()
    cp=subprocess.run(cmd,cwd=PROJECT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=OUT/(label+'.log');log.write_bytes(cp.stdout)
    record['commands'].append({'source':rel,'source_sha256':sha(PROJECT/rel),'command':cmd,
      'exit_code':cp.returncode,'elapsed_seconds':time.monotonic()-start,'log':log.name,
      'log_sha256':sha(log),'fresh_objects':{str(p.relative_to(prefix)):sha(p) for p in outputs if p.exists()}})
    save('fresh-checks.json',record);print('Exit',cp.returncode,flush=True)
    assert cp.returncode==0,cp.stdout.decode()
    assert cp.stdout.count(b'warning:')==(8 if rel=='Challenge.lean' else 0),cp.stdout.decode()
    assert cp.stdout.count(b'declaration uses `sorry`')==(8 if rel=='Challenge.lean' else 0)
    assert b'error:' not in cp.stdout

reports=[]
for filename in ['NLA-MI03-Proof.log','Solution.log']:
    for name,body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(OUT/filename).read_text()):
        axioms=[x.strip() for x in body.split(',') if x.strip()]
        assert set(axioms)=={'propext','Classical.choice','Quot.sound'},name
        reports.append({'name':name,'axioms':axioms,'log':filename})
assert len(reports)==16;save('axioms.json',{'count':16,'standard_three_only':True,'reports':reports})
inspection=(OUT/'reviews-proof-referee-2-evidence-Inspect.log').read_text()
assert 'INDEPENDENT_PROJECT_DECLARATIONS: 95' in inspection
required=re.findall(r'INDEPENDENT_RETAINED: (\S+)',inspection)
assert len(required)==31,(len(required),required)
save('actual-dependencies.json',{'project_declarations':95,'required_count':len(required),'actual_consumed':required})
after=integrity();save('integrity-after.json',after);assert before==after
record.update(status='PASS',fresh_commands=10,kernel_axiom_reports=16,actual_required_dependencies=len(required),
              exact_source_exports=8,all_frozen_inputs_unchanged=True)
save('fresh-checks.json',record)
print(json.dumps({'status':'PASS','fresh_commands':10,'standard_three_audits':16,
                 'actual_required_dependencies':len(required),'frozen_inputs':101,'originals':8}),flush=True)
