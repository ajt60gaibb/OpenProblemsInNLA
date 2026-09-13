"""Independent RA09 statement referee 2: exact inputs and fresh elaboration.
Scaffolding adapted from this reviewer's MF16 runner; no proof implementation.
"""
from pathlib import Path
import datetime, hashlib, json, os, platform, re, shutil, subprocess, tempfile, time
P = Path(__file__).resolve().parents[2]
W = P.parents[2]
E = Path(__file__).resolve().parent
L = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
C = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
freeze = P/'reviews/statement-freeze.json'
assert sha(freeze) == 'c144b68990fca06c554790b25bfaef7544c0a8baf532e5b38365fe74ee9c87ed'
assert sha(P/'reviews/statement-handoff.md') == '5ecf95acfe00db1e19165cfaa9f3ed78a097e653570664bcb47b3ee6542d118d'
f = json.loads(freeze.read_text())
standard = {'propext', 'Classical.choice', 'Quot.sound'}
def check_inputs(label):
    for name, h in f['files'].items(): assert sha(P/name) == h, name
    originals = {}
    for name, h in f['source_files'].items():
        raw = subprocess.check_output(['git', 'show', f['base']+':'+name], cwd=W)
        blob = subprocess.check_output(['git','rev-parse',f['base']+':'+name],cwd=W).decode().strip()
        assert hashlib.sha256(raw).hexdigest() == h and (W/name).read_bytes() == raw, name
        assert blob == f['source_git_blobs'][name], name
        originals[name] = {'sha256': h, 'git_blob': blob}
    assert not subprocess.check_output(['git','diff','--name-only'],cwd=W)
    assert not (P/'Solution.lean').exists()
    assert not list((P/'NLA').rglob('Proof.lean'))
    config = json.loads((P/'comparator.json').read_text())
    names = re.findall(r'^theorem\s+(\w+)',(P/'Challenge.lean').read_text(),re.M)
    assert config['theorem_names'] == ['NLA.RA09.'+n for n in names]
    assert len(names) == 17 and config['definition_names'] == []
    assert set(config['permitted_axioms']) == standard
    out = {'freeze_sha256':sha(freeze),'project_files':len(f['files']),
           'source_files':len(originals),'originals':originals,'all_preserved':True,
           'no_implementation_present':True,'comparator_names':config['theorem_names']}
    (E/(label+'.json')).write_text(json.dumps(out,indent=2)+'\n')
def check_pins(label):
    pins = []
    for dep in json.loads((P/'lake-manifest.json').read_text())['packages']:
        p = C/dep['name']; rev = subprocess.check_output(['git','rev-parse','HEAD'],cwd=p).decode().strip()
        assert rev == dep['rev'], dep['name']
        assert not subprocess.check_output(['git','status','--porcelain=v1'],cwd=p), dep['name']
        pins.append({'name':dep['name'],'path':str(p),'rev':rev,'git_clean':True})
    assert len(pins) == 10
    (E/(label+'.json')).write_text(json.dumps(pins,indent=2)+'\n')
    return pins
check_inputs('initial-integrity'); pins = check_pins('initial-pins')
prefix = Path(tempfile.mkdtemp(prefix='ra09-referee2-',dir='/tmp/nla-lean-formalization/independent-prefixes'))
order = ['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib','leancert']
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join(map(str,[prefix,*[C/n/'.lake/build/lib/lean' for n in order],L/'lib/lean']))
record = {'reviewer':'/root/formal_review_standards',
 'role':'Did not author RA09 statements or proof. Authored earlier RA08 spectral-data design, which RA09 explicitly reuses; this relationship is disclosed.',
 'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'platform':platform.platform(),
 'scope':'Fresh macOS statement elaboration only. Read-only exact MI22 dependencies; no old RA09 project objects, no Lake, dependency copying/download/build or Linux Comparator.',
 'toolchain':subprocess.check_output([str(L/'bin/lean'),'--version']).decode().strip(),
 'prefix':str(prefix),'LEAN_PATH':env['LEAN_PATH'],'pins':pins,'commands':[],'verdict':'RUNNING'}
def save(): (E/'fresh-result.json').write_text(json.dumps(record,indent=2)+'\n')
try:
    for name in ['NLA/RA09/Definitions.lean','Challenge.lean','reviews/statement-referee-2-evidence/Inspect.lean']:
        src = P/name; out = prefix/Path(name).with_suffix('.olean'); out.parent.mkdir(parents=True,exist_ok=True)
        cmd = [str(L/'bin/lean'),'-o',str(out),'-i',str(out.with_suffix('.ilean')),str(src)]
        start = time.monotonic(); r = subprocess.run(cmd,cwd=P,env=env,capture_output=True)
        log = E/name.replace('/','-').replace('.lean','.log'); log.write_bytes(r.stdout+r.stderr)
        (E/(name.replace('/','-')+'.txt')).write_bytes(src.read_bytes())
        row = {'source':name,'source_sha256':sha(src),'command':cmd,'exit_code':r.returncode,
               'seconds':time.monotonic()-start,'log':log.name,'log_sha256':sha(log)}
        record['commands'].append(row);save();print(name,r.returncode,round(row['seconds'],2),flush=True)
        if r.returncode: print(log.read_text()[-8000:],flush=True)
        assert r.returncode == 0, log
        text = log.read_text()
        if name == 'Challenge.lean':
            assert text.count('warning: declaration uses `sorry`') == 17 and text.count('warning:') == 17
        else: assert 'error:' not in text and 'warning:' not in text, log
        reports = re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]",text,re.S)
        actual = {}
        for decl, atoms in reports:
            axioms = {a.strip() for a in atoms.split(',')} - {''}
            if decl == 'NLA.RA09.concaveFrobeniusTransferConjecture':
                assert 'sorryAx' in axioms and axioms <= standard | {'sorryAx'}
            else: assert axioms <= standard,(decl,axioms)
            actual[decl] = sorted(axioms)
        if name.endswith('Inspect.lean'):
            assert len(actual) == 26, (len(actual),actual)
            row['structural_and_library_kernel_axiom_reports'] = 25
            row['intentional_reference_sorry_closure_visible'] = True
            row['axiom_reports'] = actual
    check_inputs('final-integrity');assert check_pins('final-pins') == pins
    record['verdict'] = 'PASS: frozen statement review checks only'
finally:
    record['fresh_project_objects'] = [{'path':str(q.relative_to(prefix)),'bytes':q.stat().st_size,'sha256':sha(q)} for q in sorted(prefix.rglob('*')) if q.is_file()]
    shutil.rmtree(prefix);record['disposable_prefix_removed_after_hashing'] = True
    record['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat();save()
print('INDEPENDENT STATEMENT CHECKS PASS',flush=True)
