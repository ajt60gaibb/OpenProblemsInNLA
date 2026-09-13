"""Complete fresh RA09 source check using exact clean dependencies read-only.

Adapted from the completed RA08 author validation harness.
All old RA09 objects are excluded. The reference Challenge is compiled last
and is never imported by implementation. Logs and snapshots include failures.
This local macOS check is not the authoritative Linux Comparator.
"""
from pathlib import Path
import datetime, hashlib, json, os, platform, re, shutil, subprocess, tempfile, time

P=Path(__file__).resolve().parents[2]
E=Path(__file__).resolve().parent
W=P.parents[2]
C=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
L=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
frozen=json.loads((P/'reviews/statement-freeze.json').read_text())
def preserve():
    for name,h in frozen['files'].items(): assert sha(P/name)==h,name
    for name,h in frozen['source_files'].items():
        raw=subprocess.check_output(['git','show',frozen['base']+':'+name],cwd=W)
        assert hashlib.sha256(raw).hexdigest()==h and (W/name).read_bytes()==raw,name
        assert subprocess.check_output(['git','rev-parse',frozen['base']+':'+name],cwd=W).decode().strip()==frozen['source_git_blobs'][name]
    assert not subprocess.check_output(['git','diff','--name-only'],cwd=W)
def pins_check():
    pins=[]
    for d in json.loads((P/'lake-manifest.json').read_text())['packages']:
        dep=C/d['name']
        assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=dep).decode().strip()==d['rev']
        assert not subprocess.check_output(['git','status','--porcelain=v1'],cwd=dep)
        pins.append({'name':d['name'],'rev':d['rev'],'path':str(dep),'git_clean':True})
    return pins
preserve()
pins=pins_check()
run=Path(tempfile.mkdtemp(prefix='attempt-',dir=E))
prefix=Path(tempfile.mkdtemp(prefix='ra09-final-',dir='/tmp/nla-lean-formalization/independent-prefixes'))
order=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib','leancert']
env=os.environ.copy()
env['LEAN_PATH']=':'.join(map(str,[prefix,*[C/n/'.lake/build/lib/lean' for n in order],L/'lib/lean']))
sources=['NLA/RA09/Definitions.lean', 'NLA/RA09/Frobenius.lean', 'NLA/RA09/OrderedExistence.lean', 'NLA/RA09/SpectralCFC.lean', 'NLA/RA09/Spectral.lean', 'NLA/RA09/Scalar.lean', 'NLA/RA09/Harmonic.lean', 'NLA/RA09/Overlap.lean', 'NLA/RA09/OverlapOrder.lean', 'NLA/RA09/Averaging.lean', 'NLA/RA09/TailScale.lean', 'NLA/RA09/ZeroColumn.lean', 'NLA/RA09/Transfer.lean', 'NLA/RA09/ZeroTail.lean', 'NLA/RA09/Proof.lean', 'Solution.lean', 'verification/final/Inspect.lean', 'Challenge.lean']
record={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'platform':platform.platform(),'toolchain':subprocess.check_output([str(L/'bin/lean'),'--version']).decode().strip(),
 'scope':'Fresh macOS direct source check. Ten exact clean dependency sources/artifacts reused read-only. All prior project objects excluded. No Lake build, dependency downloads/copies/rebuilds or Linux/Comparator claim.',
 'prefix':str(prefix),'LEAN_PATH':env['LEAN_PATH'],'pins':pins,'commands':[],
 'runner_sha256':sha(__file__),'verdict':'RUNNING'}
(run/'runner.py.txt').write_bytes(Path(__file__).read_bytes())
def save(): (run/'result.json').write_text(json.dumps(record,indent=2)+'\n')
try:
    for source in sources:
        f=P/source
        snapshot=run/(source.replace('/','-')+'.txt');snapshot.write_bytes(f.read_bytes())
        target=prefix/Path(source).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
        cmd=[str(L/'bin/lean'),'-o',str(target),'-i',str(target.with_suffix('.ilean')),str(f)]
        start=time.monotonic();r=subprocess.run(cmd,cwd=P,env=env,capture_output=True)
        log=run/source.replace('/','-').replace('.lean','.log');log.write_bytes(r.stdout+r.stderr)
        row={'source':source,'source_sha256':sha(f),'command':cmd,'exit_code':r.returncode,
          'seconds':time.monotonic()-start,'log':log.name,'log_sha256':sha(log)}
        record['commands'].append(row);save()
        print(source,r.returncode,round(row['seconds'],2),flush=True)
        assert r.returncode==0,log
        text=log.read_text()
        if source=='Challenge.lean':
            assert text.count('warning: declaration uses `sorry`')==17,log
            assert text.count('warning:')==17 and 'error:' not in text,log
        else: assert 'warning:' not in text and 'error:' not in text,log
        for closure in re.findall(r'depends on axioms: \[(.*?)\]',text):
            assert set(x.strip() for x in closure.split(',')) <= {'propext','Classical.choice','Quot.sound'},closure
    assert pins_check()==pins
    preserve()
    record.update({'verdict':'PASS','pins_rechecked_after':True,
      'frozen_statement_inputs_preserved':len(frozen['files']),
      'original_source_Git_blobs_preserved':len(frozen['source_files'])})
except BaseException as exc:
    record.update({'verdict':'FAIL','failure':repr(exc)})
    raise
finally:
    record['objects_hashed_before_cleanup']=[{'path':str(f.relative_to(prefix)),'bytes':f.stat().st_size,'sha256':sha(f)}
        for f in sorted(prefix.rglob('*')) if f.is_file()]
    shutil.rmtree(prefix)
    record['disposable_prefix_removed_after_check']=True
    record['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
    (E/'latest.json').write_text(json.dumps({'attempt':str(run),'result_sha256':sha(run/'result.json')},indent=2)+'\n')
print('PASS',run,flush=True)
