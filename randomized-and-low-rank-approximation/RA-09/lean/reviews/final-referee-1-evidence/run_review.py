"""Independent RA09 final referee 1 direct-source checks.
Runner layout informed by the campaign's run_fresh.py; independently verifies
both frozen inventories, uses a new target-only prefix and compares elaborated
reference signatures separately. This is macOS validation, not Comparator.
"""
from pathlib import Path
import datetime, hashlib, json, os, platform, re, subprocess, sys, tempfile, time
P=Path(__file__).resolve().parents[2]
E=Path(__file__).resolve().parent
W=P.parents[2]
C=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
L=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
sha=lambda f: hashlib.sha256(Path(f).read_bytes()).hexdigest()
state=E/'execution.json'
def freeze_check():
    counts=[]
    for rel,expected in [('verification/proof-freeze.json','533f5c328cdaf8c1f23f238f8c71b7b4b2fdabb2f532d58a398d4ab2434ccf7e'),('reviews/statement-freeze.json','c144b68990fca06c554790b25bfaef7544c0a8baf532e5b38365fe74ee9c87ed')]:
        f=P/rel; assert sha(f)==expected,rel
        data=json.loads(f.read_text())
        for name,h in data['files'].items(): assert sha(P/name)==h,name
        for name,h in data['source_files'].items():
            b=subprocess.check_output(['git','show',data['base']+':'+name],cwd=W)
            assert hashlib.sha256(b).hexdigest()==h and (W/name).read_bytes()==b,name
            assert subprocess.check_output(['git','rev-parse',data['base']+':'+name],cwd=W).decode().strip()==data['source_git_blobs'][name]
        counts.append({'path':rel,'sha256':expected,'project_inputs':len(data['files']),'source_Git_inputs':len(data['source_files'])})
    return counts
def pins():
    rows=[]
    for dep in json.loads((P/'lake-manifest.json').read_text())['packages']:
        d=C/dep['name']; commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=d).decode().strip()
        assert commit==dep['rev'],dep['name']
        assert not subprocess.check_output(['git','status','--porcelain=v1'],cwd=d),dep['name']
        rows.append({'name':dep['name'],'rev':commit,'path':str(d),'clean':True})
    return rows
phase=sys.argv[1]
if phase=='build':
    assert not state.exists()
    preserved=freeze_check(); pin=pins()
    prefix=Path(tempfile.mkdtemp(prefix='ra09-final-referee1-',dir='/tmp/nla-lean-formalization/independent-prefixes'))
    assert list(prefix.iterdir())==[]
    order=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib','leancert']
    record={'reviewer':'/root/ra09_final_referee1','role':'Independent final mathematical referee; no source authorship',
      'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'platform':platform.platform(),
      'lean_version':subprocess.check_output([str(L/'bin/lean'),'--version']).decode().strip(),
      'prefix':str(prefix),'prefix_initially_empty':True,'pins_before':pin,'frozen_before':preserved,
      'LEAN_PATH':':'.join(map(str,[prefix,*[C/n/'.lake/build/lib/lean' for n in order],L/'lib/lean'])),
      'scope':'Fresh direct source build on macOS; pinned package sources/objects read-only; no Lake/dependency download or cache mutation; not Linux Comparator.',
      'commands':[],'verdict':'RUNNING'}
    state.write_text(json.dumps(record,indent=2)+'\n')
    reference=(P/'Challenge.lean').read_text()
    assert reference.count('namespace NLA.RA09\n')==1 and reference.count('end NLA.RA09\n')==1
    reference=reference.replace('namespace NLA.RA09\n','namespace NLA.RA09.FinalReferee1Reference\n').replace('end NLA.RA09\n','end NLA.RA09.FinalReferee1Reference\n')
    (E/'Reference.lean').write_text(reference)
    (E/'reference-derivation.json').write_text(json.dumps({'source':'Challenge.lean','source_sha256':sha(P/'Challenge.lean'),'derived_sha256':sha(E/'Reference.lean'),'only_change':'namespace/end NLA.RA09 -> NLA.RA09.FinalReferee1Reference','intentional_reference_placeholders':17,'excluded_from_implementation':True},indent=2)+'\n')
    sources=['NLA/RA09/'+x+'.lean' for x in ['Definitions','Frobenius','OrderedExistence','SpectralCFC','Spectral','Scalar','Harmonic','Overlap','OverlapOrder','Averaging','TailScale','ZeroColumn','Transfer','ZeroTail','Proof']]+['Solution.lean','reviews/final-referee-1-evidence/Reference.lean']
else:
    record=json.loads(state.read_text()); prefix=Path(record['prefix'])
    assert prefix.exists()
    assert freeze_check()==record['frozen_before']
    assert pins()==record['pins_before']
    sources=['reviews/final-referee-1-evidence/Inspect.lean'] if phase=='inspect' else []
def save(): state.write_text(json.dumps(record,indent=2)+'\n')
env=os.environ.copy(); env['LEAN_PATH']=record['LEAN_PATH']
try:
    for rel in sources:
        f=P/rel; target=prefix/Path(rel).with_suffix('.olean'); target.parent.mkdir(parents=True,exist_ok=True)
        assert not target.exists(),str(target)
        lab=rel.replace('/','-').replace('.lean','')
        (E/(lab+'.source.txt')).write_bytes(f.read_bytes())
        cmd=[str(L/'bin/lean'),'-o',str(target),'-i',str(target.with_suffix('.ilean')),str(f)]
        started=time.monotonic(); run=subprocess.run(cmd,cwd=P,env=env,capture_output=True)
        log=E/(lab+'.log'); log.write_bytes(run.stdout+run.stderr)
        record['commands'].append({'source':rel,'sha256':sha(f),'command':cmd,'exit_code':run.returncode,
          'seconds':round(time.monotonic()-started,3),'log':log.name,'log_sha256':sha(log)})
        save(); print(rel,run.returncode,record['commands'][-1]['seconds'],flush=True)
        assert run.returncode==0,str(log)
        output=log.read_text()
        if rel.endswith('/Reference.lean'):
            assert output.count('warning: declaration uses `sorry`')==17 and output.count('warning:')==17
        else: assert 'warning:' not in output and 'error:' not in output,str(log)
        for closure in re.findall(r'depends on axioms: \[(.*?)\]',output):
            assert set(x.strip() for x in closure.split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'},closure
    assert freeze_check()==record['frozen_before']
    assert pins()==record['pins_before']
    record['frozen_after']=record['frozen_before']; record['pins_after']=record['pins_before']
    record['phase_completed']=phase; record['verdict']='PASS_LOCAL_SOURCE' if phase=='build' else 'PASS_LOCAL_SOURCE_AND_INSPECTION'
    if phase=='cleanup':
        generated=[{'path':str(f.relative_to(prefix)),'sha256':sha(f),'bytes':f.stat().st_size} for f in sorted(prefix.rglob('*')) if f.is_file()]
        record['generated_before_cleanup']=generated; save()
        for row in generated:
            f=prefix/row['path']; assert sha(f)==row['sha256']; f.unlink()
        for d in sorted([p for p in prefix.rglob('*') if p.is_dir()],key=lambda p:len(p.parts),reverse=True):d.rmdir()
        prefix.rmdir(); record['only_recorded_generated_objects_removed']=True
except BaseException as exc:
    record['verdict']='FAIL'; record['failure']=repr(exc); save(); raise
record['last_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat(); record['runner_sha256']=sha(__file__); save()
