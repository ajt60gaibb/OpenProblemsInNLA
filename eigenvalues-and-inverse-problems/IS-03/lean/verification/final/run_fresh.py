"""Fresh IS03 proof/source elaboration; pinned dependency cache is read-only."""
from pathlib import Path
import datetime, hashlib, json, os, platform, re, subprocess, tempfile, time

P = Path(__file__).resolve().parents[2]
E = Path(__file__).resolve().parent
W = P.parents[2]
C = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
L = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
freeze = json.loads((P/'reviews/statement-freeze.json').read_text())

def preserved():
    for name, expected in freeze['files'].items():
        assert sha(P/name) == expected, name
    for name, expected in freeze['source_files'].items():
        original = subprocess.check_output(['git', 'show', freeze['base']+':'+name], cwd=W)
        assert hashlib.sha256(original).hexdigest() == expected
        assert (W/name).read_bytes() == original, name
    assert not subprocess.check_output(['git', 'diff', '--name-only'], cwd=W)

preserved()
pins = []
for dep in json.loads((P/'lake-manifest.json').read_text())['packages']:
    path = C/dep['name']
    actual = subprocess.check_output(['git','rev-parse','HEAD'],cwd=path).decode().strip()
    assert actual == dep['rev'], dep['name']
    assert not subprocess.check_output(['git','status','--porcelain=v1'],cwd=path)
    pins.append({'name':dep['name'],'path':str(path.resolve()),'rev':actual,'clean':True})
run = Path(tempfile.mkdtemp(prefix='attempt-',dir=E))
prefix = Path(tempfile.mkdtemp(prefix='is03-final-',
    dir='/tmp/nla-lean-formalization/independent-prefixes'))
order=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient',
       'plausible','mathlib','leancert']
env=os.environ.copy()
env['LEAN_PATH']=':'.join(map(str,[prefix,*[C/n/'.lake/build/lib/lean' for n in order],L/'lib/lean']))
record={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'platform':platform.platform(),'toolchain':subprocess.check_output([str(L/'bin/lean'),'--version']).decode().strip(),
    'scope':'Fresh local macOS source elaboration, all project objects excluded initially. Ten exact pinned clean dependency source/artifact caches reused read-only. No dependency clone/copy/rebuild, Lake build, Linux execution, or Comparator result claimed.',
    'prefix':str(prefix),'LEAN_PATH':env['LEAN_PATH'],'pins':pins,'commands':[]}
sources=['NLA/IS03/Definitions.lean','NLA/IS03/Algebra.lean','NLA/IS03/Witness.lean',
    'NLA/IS03/Spectral.lean','NLA/IS03/Newton.lean','NLA/IS03/Numerical.lean',
    'NLA/IS03/Proof.lean','Solution.lean','verification/final/Inspect.lean','Challenge.lean']
for source in sources:
    file=P/source
    (run/(source.replace('/','-')+'.txt')).write_bytes(file.read_bytes())
    target=prefix/Path(source).with_suffix('.olean')
    target.parent.mkdir(parents=True,exist_ok=True)
    cmd=[str(L/'bin/lean'),'-o',str(target),'-i',str(target.with_suffix('.ilean')),str(file)]
    start=time.monotonic()
    result=subprocess.run(cmd,cwd=P,env=env,capture_output=True)
    output=result.stdout+result.stderr
    log=run/(source.replace('/','-').replace('.lean','.log'))
    log.write_bytes(output)
    row={'source':source,'sha256':sha(file),'command':cmd,'exit_code':result.returncode,
         'seconds':time.monotonic()-start,'log':log.name,'log_sha256':sha(log)}
    record['commands'].append(row)
    (run/'result.json').write_text(json.dumps(record,indent=2)+'\n')
    print(source,result.returncode,round(row['seconds'],2),flush=True)
    if result.returncode:
        print(output.decode()[:8000],flush=True)
        raise SystemExit(result.returncode)
    if source=='Challenge.lean':
        assert output.decode().count('warning: declaration uses `sorry`')==7
    else:
        assert 'warning:' not in output.decode() and 'error:' not in output.decode(), log
    for closure in re.findall(r'depends on axioms: \[(.*?)\]',output.decode()):
        assert set(x.strip() for x in closure.split(',')) <= {'propext','Classical.choice','Quot.sound'},closure
for dep in pins:
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=dep['path']).decode().strip()==dep['rev']
    assert not subprocess.check_output(['git','status','--porcelain=v1'],cwd=dep['path'])
preserved()
record.update({'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'verdict':'PASS: complete local source proofs and actual dependency audit',
    'frozen_statement_inputs_preserved':len(freeze['files']),
    'original_source_blobs_preserved':len(freeze['source_files']),
    'pins_rechecked_after':True})
(run/'result.json').write_text(json.dumps(record,indent=2)+'\n')
(E/'latest.json').write_text(json.dumps({'attempt':str(run),'prefix':str(prefix),
    'result_sha256':sha(run/'result.json')},indent=2)+'\n')
print('PASS',run,flush=True)
