"""Independent RA09 referee2 fresh source validation. Runner architecture adapted
from the reviewed author run_fresh.py; evidence, prefix and actual execution are
independent. All frozen proof inputs are checked before and after the run.
No Lake invocation, no cache write/download/copy, no local Linux claim.
"""
from pathlib import Path
import datetime,hashlib,json,os,platform,re,shutil,subprocess,tempfile,time,traceback
E=Path(__file__).resolve().parent;P=E.parents[1];W=P.parents[2]
C=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
L=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
expected='533f5c328cdaf8c1f23f238f8c71b7b4b2fdabb2f532d58a398d4ab2434ccf7e'
assert sha(P/'verification/proof-freeze.json')==expected
freeze=json.loads((P/'verification/proof-freeze.json').read_text())
assert sha(P/'reviews/statement-freeze.json')==freeze['statement_freeze_sha256']
assert sha(P/'verification/proof-start.json')==freeze['accepted_statement_gate_sha256']
def preserve(label):
    for name,h in freeze['files'].items(): assert sha(P/name)==h,name
    rows={}
    for name,h in freeze['source_files'].items():
        raw=subprocess.check_output(['git','show',freeze['base']+':'+name],cwd=W)
        assert hashlib.sha256(raw).hexdigest()==h and (W/name).read_bytes()==raw,name
        blob=subprocess.check_output(['git','rev-parse',freeze['base']+':'+name],cwd=W).decode().strip()
        assert blob==freeze['source_git_blobs'][name]
        rows[name]={'sha256':h,'git_blob':blob,'bytes':len(raw)}
    report={'proof_freeze_sha256':expected,'project_frozen_files':len(freeze['files']),
      'original_source_files':rows,'all_preserved':True,
      'canonical_status':'Solved, unchanged','head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=W).decode().strip()}
    assert '**Status:** Solved' in (P.parent/'README.md').read_text()
    (E/('integrity-'+label+'.json')).write_text(json.dumps(report,indent=2)+'\n')
    return report
def pins_check(label):
    rows=[]
    for d in json.loads((P/'lake-manifest.json').read_text())['packages']:
        dep=C/d['name']; actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=dep).decode().strip()
        status=subprocess.check_output(['git','status','--porcelain=v1'],cwd=dep).decode()
        assert actual==d['rev'] and not status,d['name']
        rows.append({'name':d['name'],'rev':actual,'path':str(dep),'status':status})
    (E/('dependency-pins-'+label+'.json')).write_text(json.dumps(rows,indent=2)+'\n')
    return rows
before=preserve('before'); pins=pins_check('before')
prefix=Path(tempfile.mkdtemp(prefix='ra09-final-referee2-',dir='/tmp/nla-lean-formalization/independent-prefixes'))
assert not list(prefix.iterdir())
order=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib','leancert']
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[prefix,*[C/n/'.lake/build/lib/lean' for n in order],L/'lib/lean']))
names=['Definitions','Frobenius','OrderedExistence','SpectralCFC','Spectral','Scalar','Harmonic','Overlap','OverlapOrder','Averaging','TailScale','ZeroColumn','Transfer','ZeroTail','Proof']
sources=['NLA/RA09/'+n+'.lean' for n in names]+['Solution.lean',
 'reviews/final-referee-2-evidence/Reference.lean','reviews/final-referee-2-evidence/Inspect.lean','reviews/final-referee-2-evidence/Consumer.lean']
record={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'reviewer':'/root/mf16_final_referee','scope':'Independent fresh macOS source compilation with read-only exact MI22 dependency sources/artifacts; no earlier project objects, no Lake, no Linux Comparator or standalone kernel replay claim.',
 'platform':platform.platform(),'toolchain':subprocess.check_output([str(L/'bin/lean'),'--version']).decode().strip(),
 'lean_binary_sha256':sha(L/'bin/lean'),'prefix':str(prefix),'prefix_initially_empty':True,
 'LEAN_PATH':env['LEAN_PATH'],'pins':pins,'commands':[],'runner_sha256':sha(__file__),'verdict':'RUNNING'}
def save(): (E/'fresh-result.json').write_text(json.dumps(record,indent=2)+'\n')
save()
try:
    for source in sources:
        f=P/source; stem=source.replace('/','-').removesuffix('.lean')
        snapshot=E/(stem+'.lean.txt');snapshot.write_bytes(f.read_bytes())
        target=prefix/Path(source).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
        cmd=[str(L/'bin/lean'),'-o',str(target),'-i',str(target.with_suffix('.ilean')),str(f)]
        t=time.monotonic(); r=subprocess.run(cmd,cwd=P,env=env,capture_output=True)
        log=E/(stem+'.log');log.write_bytes(r.stdout+r.stderr)
        row={'source':source,'source_sha256':sha(f),'command':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-t,
          'log':log.name,'log_sha256':sha(log),'source_snapshot':snapshot.name}
        record['commands'].append(row); save(); print(source,r.returncode,round(row['seconds'],2),flush=True)
        assert r.returncode==0,log
        text=log.read_text()
        if source.endswith('/Reference.lean'):
            assert text.count('warning: declaration uses `sorry`')==17 and text.count('warning:')==17 and 'error:' not in text,log
        else: assert 'warning:' not in text and 'error:' not in text,log
        for ax in re.findall(r'depends on axioms: \[(.*?)\]',text):
            assert set(x.strip() for x in ax.split(','))<={'propext','Classical.choice','Quot.sound'},ax
    assert pins_check('after')==pins
    assert preserve('after')==before
    record['verdict']='PASS'
except BaseException as exc:
    record['verdict']='FAIL'; record['failure']=repr(exc)
    (E/'raw-failure.txt').write_text(traceback.format_exc())
    raise
finally:
    record['objects_hashed_before_cleanup']=[{'path':str(f.relative_to(prefix)),'bytes':f.stat().st_size,'sha256':sha(f)} for f in sorted(prefix.rglob('*')) if f.is_file()]
    # Only this reviewer-created disposable target prefix is eligible for cleanup.
    # Keep failed-run objects for focused diagnostic correction without rebuilding.
    if record['verdict']=='PASS':
        shutil.rmtree(prefix);record['disposable_prefix_removed_after_check']=True
    else: record['disposable_prefix_removed_after_check']=False
    record['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
print('PASS: independent fresh source checks complete',flush=True)
