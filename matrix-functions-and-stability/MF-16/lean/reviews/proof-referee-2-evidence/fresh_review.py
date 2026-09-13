"""Independent MF16 final referee 2 fresh source and trust checks."""
from pathlib import Path
import datetime,hashlib,json,os,platform,re,shutil,subprocess,tempfile,time
P=Path(__file__).resolve().parents[2]
W=P.parents[2]
E=Path(__file__).resolve().parent
L=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
C=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
freeze=P/'verification/proof-freeze.json'
assert sha(freeze)=='f4b21be066d0e55e56aae5b3fd1119433ef09d7ed5822d57dacab906b38ac720'
f=json.loads(freeze.read_text());sf=json.loads((P/'reviews/statement-freeze.json').read_text())
def check_inputs(label):
    for mapping in [f['files'],sf['files']]:
        for name,h in mapping.items(): assert sha(P/name)==h,name
    originals={}
    for name,h in f['source_files'].items():
        raw=subprocess.check_output(['git','show',f['base']+':'+name],cwd=W)
        assert hashlib.sha256(raw).hexdigest()==h and (W/name).read_bytes()==raw,name
        originals[name]={'sha256':h,'Git_blob':subprocess.check_output(['git','rev-parse',f['base']+':'+name],cwd=W).decode().strip()}
    assert not subprocess.check_output(['git','diff','--name-only'],cwd=W)
    (E/(label+'.json')).write_text(json.dumps({'proof_freeze_sha256':sha(freeze),'project_files':len(f['files']),
      'statement_files':len(sf['files']),'originals':originals,'all_preserved':True},indent=2)+'\n')
def check_pins(label):
    pins=[]
    for d in json.loads((P/'lake-manifest.json').read_text())['packages']:
        q=C/d['name'];rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=q).decode().strip()
        assert rev==d['rev'];assert not subprocess.check_output(['git','status','--porcelain=v1'],cwd=q)
        pins.append({'name':d['name'],'path':str(q),'rev':rev,'git_clean':True})
    (E/(label+'.json')).write_text(json.dumps(pins,indent=2)+'\n');return pins
check_inputs('initial-integrity');pins=check_pins('initial-pins')
prefix=Path(tempfile.mkdtemp(prefix='mf16-referee2-',dir='/tmp/nla-lean-formalization/independent-prefixes'))
order=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib','leancert']
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[prefix,*[C/n/'.lake/build/lib/lean' for n in order],L/'lib/lean']))
record={'reviewer':'/root/formal_review_standards','author_of_reviewed_proof_or_statements':False,
 'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'platform':platform.platform(),
 'scope':'Independent fresh macOS source elaboration. Shared MI22 exact dependency source/artifacts read-only. No prior MF16 project objects, dependency download/copy/rebuild, Lake or Linux Comparator run.',
 'toolchain':subprocess.check_output([str(L/'bin/lean'),'--version']).decode().strip(),
 'prefix':str(prefix),'LEAN_PATH':env['LEAN_PATH'],'pins':pins,'commands':[],'verdict':'RUNNING'}
sources=['NLA/MF16/Definitions.lean','NLA/MF16/Numerical.lean','NLA/MF16/Algebra.lean',
 'NLA/MF16/Recovery.lean','NLA/MF16/Polynomial.lean','NLA/MF16/CayleyHamilton.lean',
 'NLA/MF16/Proof.lean','Solution.lean','reviews/proof-referee-2-evidence/Inspect.lean','Challenge.lean']
def save(): (E/'fresh-result.json').write_text(json.dumps(record,indent=2)+'\n')
try:
    for name in sources:
        src=P/name;out=prefix/Path(name).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
        cmd=[str(L/'bin/lean'),'-o',str(out),'-i',str(out.with_suffix('.ilean')),str(src)]
        start=time.monotonic();r=subprocess.run(cmd,cwd=P,env=env,capture_output=True)
        log=E/name.replace('/','-').replace('.lean','.log');log.write_bytes(r.stdout+r.stderr)
        row={'source':name,'source_sha256':sha(src),'command':cmd,'exit_code':r.returncode,
          'seconds':time.monotonic()-start,'log':log.name,'log_sha256':sha(log)}
        record['commands'].append(row);save();print(name,r.returncode,round(row['seconds'],2),flush=True)
        if r.returncode: print(log.read_text()[-6000:],flush=True)
        assert r.returncode==0,log
        text=log.read_text()
        if name=='Challenge.lean': assert text.count('warning: declaration uses `sorry`')==9 and text.count('warning:')==9
        else: assert 'error:' not in text and 'warning:' not in text,log
        for a in re.findall(r'depends on axioms: \[(.*?)\]',text):
            assert set(a.split(', ')) - {''} <= {'propext','Classical.choice','Quot.sound'},a
    check_inputs('final-integrity');assert check_pins('final-pins')==pins
    record['verdict']='PASS'
finally:
    record['project_object_hashes']=[{'path':str(p.relative_to(prefix)),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(prefix.rglob('*')) if p.is_file()]
    shutil.rmtree(prefix);record['disposable_prefix_removed_after_check']=True
    record['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
print('INDEPENDENT FRESH PASS',flush=True)
