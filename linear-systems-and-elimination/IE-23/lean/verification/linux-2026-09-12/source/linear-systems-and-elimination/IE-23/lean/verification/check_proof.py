"""Fresh author IE23 proof, export, trust and actual-dependency checks.

Adapted from the campaign's MI22/MI03 fresh-prefix drivers. Dependency sources
and objects are reused read-only from MI22 at the exact same manifest pins.
Every project module is freshly compiled; no previous project object is used.
This is author macOS evidence, not independent review or a Linux/Comparator run.
"""
from pathlib import Path
import datetime,hashlib,json,os,platform,re,subprocess,tempfile,time
P=Path(__file__).resolve().parents[1]
REPO=P.parents[2]
OUT=P/'verification/final-author'
OUT.mkdir(exist_ok=True)
D=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
B=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin')
sha=lambda path:hashlib.sha256(Path(path).read_bytes()).hexdigest()
save=lambda name,data:(OUT/name).write_text(json.dumps(data,indent=2)+'\n')
start=json.loads((P/'verification/proof-start.json').read_text())
assert sha(P/'verification/proof-start.json')=='7380aff57e428652e86548d6f1ad535a175d1fc8b1da1b3009092bdd6a868fec'

def integrity():
    for rel,digest in start['records'].items():assert sha(P/rel)==digest,rel
    for rel,digest in start['approved_project_inputs'].items():assert sha(P/rel)==digest,rel
    f=json.loads((P/'reviews/statement-freeze.json').read_text())
    for rel,digest in start['approved_original_inputs'].items():
        raw=subprocess.check_output(['git','show',f['base']+':'+rel],cwd=REPO)
        assert sha(REPO/rel)==digest and (REPO/rel).read_bytes()==raw,rel
    return {'status':'PASS','original_project_files':start['approved_project_inputs'],
     'original_source_files':start['approved_original_inputs'],
     'approved_config_and_reports':start['records'],
     'proof_start_record_sha256':sha(P/'verification/proof-start.json')}
before=integrity();save('integrity-before.json',before)
modules=['NLA/IE23/Definitions.lean','NLA/IE23/Norms.lean','NLA/IE23/Matrices.lean',
         'NLA/IE23/FourthPower.lean','NLA/IE23/Actions.lean','NLA/IE23/Minimizers.lean',
         'NLA/IE23/Proof.lean','Solution.lean']
inputs={rel:sha(P/rel) for rel in modules+['verification/InspectProof.lean','PROOF_MAP.md']}
for rel in modules:
    text=(P/rel).read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',text),rel
    assert not re.search(r'^import\s+Challenge\b',text,re.M),rel

def signatures(text):
    return {n:' '.join(s.split()) for n,s in re.findall(r'theorem\s+(\w+)\s+(.*?)\s*:=\s*by',text,re.S)}
ch=signatures((P/'Challenge.lean').read_text())
sol=signatures((P/'Solution.lean').read_text())
cfg=json.loads((P/'comparator.json').read_text())
assert len(ch)==len(sol)==8 and ch==sol
assert cfg['theorem_names']==['NLA.IE23.'+n for n in sol]
assert cfg['definition_names']==[]
assert cfg['permitted_axioms']==['propext','Classical.choice','Quot.sound']
save('source-signatures.json',{'status':'PASS','count':8,'signatures':sol,
     'scope':'Exact normalized source signatures; actual isolated Linux Comparator remains separate.'})

pins=[]
for pkg in json.loads((P/'lake-manifest.json').read_text())['packages']:
    path=D/pkg['name']
    rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=path,text=True).strip()
    dirty=subprocess.check_output(['git','status','--porcelain'],cwd=path,text=True)
    assert rev==pkg['rev'] and not dirty,(pkg['name'],rev,dirty)
    pins.append({'name':pkg['name'],'path':str(path),'revision':rev,'git_status_porcelain':dirty})
assert len(pins)==10;save('dependency-pins.json',pins)
prefix=Path(tempfile.mkdtemp(prefix='ie23-author-final-',dir=P/'.verification'))
paths=[str(prefix)]+[str(D/x['name']/'.lake/build/lib/lean') for x in reversed(pins)]+[str(B.parent/'lib/lean')]
env=dict(os.environ,LEAN_PATH=os.pathsep.join(paths))
record={'status':'RUNNING','phase':'fresh-author-proof-check','date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'platform':platform.platform(),'lean_version':subprocess.check_output([str(B/'lean'),'--version'],text=True).strip(),
 'dependency_root':str(D),'read_only_matching_dependency_objects_reused':True,
 'dependency_sources_rebuilt':False,'old_project_objects_excluded':True,
 'fresh_prefix':str(prefix),'LEAN_PATH':env['LEAN_PATH'],'source_inputs':inputs,
 'local_lake_invocation':False,'Linux_Comparator_run':False,'independent_referee':False,'commands':[]}
for rel in modules+['Challenge.lean','verification/InspectProof.lean']:
    cmd=[str(B/'lean')]
    objects=[]
    if rel!='verification/InspectProof.lean':
        for flag,suffix in [('-o','.olean'),('-i','.ilean')]:
            dest=prefix/Path(rel).with_suffix(suffix);dest.parent.mkdir(parents=True,exist_ok=True)
            cmd.extend([flag,str(dest)]);objects.append(dest)
    cmd.append(rel)
    label=rel.removesuffix('.lean').replace('/','-')
    print('Fresh checking',rel,flush=True);t=time.monotonic()
    cp=subprocess.run(cmd,cwd=P,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=OUT/(label+'.log');log.write_bytes(cp.stdout)
    record['commands'].append({'source':rel,'source_sha256':sha(P/rel),'command':cmd,
     'exit_code':cp.returncode,'elapsed_seconds':time.monotonic()-t,
     'log':log.name,'log_sha256':sha(log),
     'fresh_objects':{str(x.relative_to(prefix)):sha(x) for x in objects if x.exists()}})
    save('fresh-checks.json',record)
    print('Exit',cp.returncode,flush=True)
    assert cp.returncode==0,cp.stdout.decode()
    holes=8 if rel=='Challenge.lean' else 0
    assert cp.stdout.count(b'warning:')==holes,cp.stdout.decode()
    assert cp.stdout.count(b'declaration uses `sorry`')==holes,cp.stdout.decode()
    assert b'error:' not in cp.stdout

reports=[]
for name in ['NLA-IE23-Proof.log','Solution.log']:
    for declaration,body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(OUT/name).read_text()):
        axioms=[x.strip() for x in body.split(',') if x.strip()]
        assert set(axioms)=={'propext','Classical.choice','Quot.sound'},declaration
        reports.append({'name':declaration,'axioms':axioms,'log':name})
assert len(reports)==16
save('axioms.json',{'count':16,'all_standard_three_only':True,'reports':reports})
raw=(OUT/'verification-InspectProof.log').read_text()
required=re.findall(r'^ACTUAL_RETAINED: (\S+)',raw,re.M)
count=int(re.search(r'^ACTUAL_PROJECT_DECLARATIONS: (\d+)',raw,re.M).group(1))
assert len(required)==38 and count==93,(len(required),count)
save('actual-dependencies.json',{'reached_project_declarations':count,'required_count':len(required),'actual_consumed':required})
after=integrity();save('integrity-after.json',after);assert before==after
assert inputs=={rel:sha(P/rel) for rel in inputs}
record.update(status='PASS',fresh_commands=10,axiom_audits=16,exact_exports=8,
              reached_project_declarations=count,required_dependencies=len(required),
              original_frozen_inputs_unchanged=True,proof_inputs_unchanged=True)
save('fresh-checks.json',record)
print(json.dumps({'status':'PASS','fresh_commands':10,'exact_exports':8,'standard_three':16,
 'project_declarations':count,'material_dependencies':len(required),'pins':10}),flush=True)
