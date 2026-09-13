"""Fresh harmonic helper checks in the same owned prefix; no dependency rebuild.
Adapted from the completed scalar helper runner.
Existing generated prefix objects are hashed then removed before fresh source
elaboration. This is local helper validation, not independent/Linux verification.
"""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,tempfile,time
E=Path(__file__).resolve().parent;P=E.parents[1];W=P.parents[2]
C=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
L=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
f=json.loads((P/'reviews/statement-freeze.json').read_text())
def preserved():
    for name,h in f['files'].items():assert sha(P/name)==h,name
    for name,h in f['source_files'].items():
        raw=subprocess.check_output(['git','show',f['base']+':'+name],cwd=W)
        assert (W/name).read_bytes()==raw and sha(W/name)==h,name
def get_pins():
    pins=[]
    for dep in json.loads((P/'lake-manifest.json').read_text())['packages']:
        q=C/dep['name'];rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=q).decode().strip()
        assert rev==dep['rev'] and not subprocess.check_output(['git','status','--porcelain=v1'],cwd=q)
        pins.append({'name':dep['name'],'rev':rev,'git_clean':True,'path':str(q)})
    return pins
preserved();pins=get_pins()
state=json.loads((E/'development-state.json').read_text());prefix=Path(state['prefix'])
assert prefix.parent==Path('/tmp/nla-lean-formalization/independent-prefixes') and prefix.name.startswith('ra09-harmonic-')
prior=[]
for p in sorted(prefix.rglob('*')):
    if p.is_file():
        assert p.suffix in {'.olean','.ilean'},p
        prior.append({'path':str(p.relative_to(prefix)),'sha256':sha(p),'bytes':p.stat().st_size});p.unlink()
assert not any(p.is_file() for p in prefix.rglob('*'))
attempt=Path(tempfile.mkdtemp(prefix='final-',dir=E))
order=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib','leancert']
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[prefix,*[C/n/'.lake/build/lib/lean' for n in order],L/'lib/lean']))
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Fresh helper source checks after removing only own generated project objects. macOS; not independent final review or Linux Comparator.',
 'prefix':str(prefix),'LEAN_PATH':env['LEAN_PATH'],'pins':pins,'removed_prior_object_hashes':prior,
 'commands':[],'result':'RUNNING'}
try:
    for name in ['NLA/RA09/Definitions.lean','NLA/RA09/Harmonic.lean','Challenge.lean','verification/harmonic-development/Inspect.lean']:
        source=P/name;out=prefix/Path(name).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
        (attempt/(name.replace('/','-')+'.txt')).write_bytes(source.read_bytes())
        cmd=[str(L/'bin/lean'),'-o',str(out),'-i',str(out.with_suffix('.ilean')),str(source)]
        start=time.monotonic();r=subprocess.run(cmd,cwd=P,env=env,capture_output=True)
        log=attempt/name.replace('/','-').replace('.lean','.log');log.write_bytes(r.stdout+r.stderr)
        row={'source':name,'source_sha256':sha(source),'command':cmd,'exit_code':r.returncode,
         'seconds':time.monotonic()-start,'log':log.name,'log_sha256':sha(log)}
        record['commands'].append(row);(attempt/'result.json').write_text(json.dumps(record,indent=2)+'\n')
        print(name,r.returncode,round(row['seconds'],2),flush=True)
        if r.returncode:print(log.read_text()[-18000:],flush=True)
        assert r.returncode==0,log
        text=log.read_text()
        if name=='Challenge.lean':assert text.count('warning: declaration uses `sorry`')==17 and text.count('warning:')==17
        else:assert 'warning:' not in text and 'error:' not in text,log
        reports=re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]",text,re.S)
        for decl,aa in reports:
            assert {a.strip() for a in aa.split(',')}-{''} <= {'propext','Classical.choice','Quot.sound'},(decl,aa)
        row['kernel_standard_three_reports']=len(reports)
    inspect=(attempt/'verification-harmonic-development-Inspect.log').read_text()
    assert inspect.count('EXACT_FROZEN_TYPE ')==1
    assert inspect.count('RETAINED ')==9
    record['reachable_project_declarations']=int(re.search(r'HARMONIC_PROJECT_COUNT (\d+)',inspect).group(1))
    preserved();assert get_pins()==pins
    record['preserved_project_inputs']=len(f['files']);record['preserved_original_source_Git_blobs']=len(f['source_files'])
    record['result']='PASS'
finally:
    record['fresh_object_hashes']=[{'path':str(p.relative_to(prefix)),'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(prefix.rglob('*')) if p.is_file()]
    (attempt/'result.json').write_text(json.dumps(record,indent=2)+'\n')
    (E/'final-latest.json').write_text(json.dumps({'attempt':str(attempt),'result_sha256':sha(attempt/'result.json')},indent=2)+'\n')
print(attempt,record['result'],flush=True)
