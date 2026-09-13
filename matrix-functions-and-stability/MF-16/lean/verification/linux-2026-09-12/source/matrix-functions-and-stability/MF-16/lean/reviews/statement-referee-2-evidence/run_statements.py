from pathlib import Path
import datetime, hashlib, json, os, platform, re, subprocess, tempfile, time

R = Path('/tmp/nla-lean-mf16-worktree')
P = R / 'matrix-functions-and-stability/MF-16/lean'
E = P / 'reviews/statement-referee-2-evidence'
C = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
L = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
E.mkdir(exist_ok=False)
(E / 'run_statements.py').write_bytes(Path(__file__).read_bytes())
freeze = json.loads((P / 'reviews/statement-freeze.json').read_text())
assert sha(P / 'reviews/statement-freeze.json') == 'eaba8311f143727f2061f2b4c945e403e62b7e9041712d983ef56ccf2e7f0587'
def frozen():
    for f, h in freeze['files'].items():
        assert sha(P / f) == h, f
    for f, h in freeze['source_files'].items():
        assert sha(R / f) == h, f
        data = subprocess.check_output(['git', 'show', f"{freeze['base']}:{f}"], cwd=R)
        assert hashlib.sha256(data).hexdigest() == h, f
        assert subprocess.check_output(['git', 'rev-parse', f"{freeze['base']}:{f}"], cwd=R).decode().strip() == freeze['source_git_blobs'][f]
    assert not (P / 'NLA/MF16/Proof.lean').exists() and not (P / 'Solution.lean').exists()
frozen()
names = json.loads((P / 'comparator.json').read_text())['theorem_names']
definitions = ['WordUniquenessConjecture', 'SymmetricWord', 'evalWord', 'symmetricMatrix', 'complexify', 'polynomialSystem', 'rootBox', 'rootCertificate', 'contractionBound']
inspect = '''/- Independent statement referee 2. Machine diagnostics are not kernel certificates. -/
import Challenge
import LeanCert.Tactic.Verification
set_option autoImplicit false
set_option pp.universes false
open scoped ComplexOrder
namespace NLA.MF16.RootStatementReview
open LeanCert.Core LeanCert.Engine NLA.MF16
set_option pp.all true in
#print NLA.MF16.WordUniquenessConjecture
#print NLA.MF16.SymmetricWord
set_option pp.all true in
#print NLA.MF16.evalWord
#print NLA.MF16.complexify
#print Matrix.PosDef
#print LeanCert.Engine.FinBoxMem
#print LeanCert.Engine.SystemZero
#check LeanCert.Engine.krawczykCheck_sound
#check LeanCert.Engine.fixedPoint_iff_systemZero
#check Matrix.aeval_self_charpoly
def ratJson (q : ℚ) : Lean.Json := .str (toString q.num ++ "/" ++ toString q.den)
def expressionJson : Expr → Lean.Json
  | .const q => .arr #[.str "constant", ratJson q]
  | .var i => .arr #[.str "variable", .num i]
  | .add a b => .arr #[.str "add", expressionJson a, expressionJson b]
  | .mul a b => .arr #[.str "multiply", expressionJson a, expressionJson b]
  | .neg a => .arr #[.str "negate", expressionJson a]
  | _ => .str "UNSUPPORTED"
def intervalJson (i : IntervalRat) : Lean.Json := .arr #[ratJson i.lo, ratJson i.hi]
#eval IO.println ("ROOT_AST=" ++ (Lean.Json.arr ((List.ofFn polynomialSystem).map expressionJson).toArray).compress)
#eval IO.println ("ROOT_CENTER=" ++ (Lean.Json.arr ((List.ofFn rootCenter).map ratJson).toArray).compress)
#eval IO.println ("ROOT_BOX=" ++ (Lean.Json.arr ((List.ofFn rootBox).map intervalJson).toArray).compress)
#eval IO.println ("ROOT_C=" ++ (Lean.Json.arr (List.ofFn fun i => Lean.Json.arr ((List.ofFn (rootCertificate.preconditioner i)).map ratJson).toArray).toArray).compress)
#eval IO.println ("ROOT_J=" ++ (Lean.Json.arr (List.ofFn fun i => Lean.Json.arr ((List.ofFn (intervalJacobian polynomialSystem rootBox {} i)).map intervalJson).toArray).toArray).compress)
#eval IO.println ("ROOT_IMAGE=" ++ (Lean.Json.arr ((List.ofFn (newtonImageEnclosure polynomialSystem rootBox rootCenter rootCertificate.preconditioner {})).map intervalJson).toArray).compress)
#eval IO.println ("ROOT_Q=" ++ (ratJson contractionBound).compress)
#eval IO.println ("ROOT_CHECK=" ++ toString (krawczykCheck polynomialSystem rootBox rootCertificate {}))
#eval IO.println ("ROOT_DET=" ++ (ratJson rootCertificate.preconditioner.det).compress)
#eval IO.println ("ROOT_RADIUS=" ++ (ratJson (boxRadius rootBox rootCenter)).compress)
#assert_trust kernel LeanCert.Engine.krawczykCheck_sound
#print axioms LeanCert.Engine.krawczykCheck_sound
'''
for n in names: inspect += '#check ' + n + '\n'
for n in definitions:
    inspect += '#assert_trust kernel NLA.MF16.' + n + '\n#print axioms NLA.MF16.' + n + '\n'
inspect += '#print axioms NLA.MF16.not_wordUniquenessConjecture\nend NLA.MF16.RootStatementReview\n'
(E / 'Inspect.lean').write_text(inspect)
manifest = json.loads((P / 'lake-manifest.json').read_text())
pins = []
def pins_ok():
    for package in manifest['packages']:
        path = C / package['name']
        assert subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD']).decode().strip() == package['rev']
        assert not subprocess.check_output(['git', '-C', str(path), 'status', '--porcelain=v1'])
pins_ok()
for package in manifest['packages']:
    pins.append({'name': package['name'], 'path': str((C / package['name']).resolve()), 'rev': package['rev'], 'clean': True})
prefix = Path(tempfile.mkdtemp(prefix='mf16-root-statements-', dir='/tmp/nla-lean-formalization/independent-prefixes'))
order = ['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib','leancert']
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join(map(str, [prefix, *[(C / n / '.lake/build/lib/lean').resolve() for n in order], L / 'lib/lean']))
record = {'reviewer': '/root', 'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'platform': platform.platform(), 'fresh_prefix': str(prefix), 'LEAN_PATH': env['LEAN_PATH'], 'pins': pins,
    'scope': 'Three fresh macOS statement-only commands. No previous project objects, local Lake build, dependency copy/download, proof implementation, kernel candidate certificate or Linux run.',
    'statement_freeze_sha256': sha(P / 'reviews/statement-freeze.json'),
    'toolchain': subprocess.check_output([str(L / 'bin/lean'), '--version']).decode().strip(), 'commands': []}
for source in ['NLA/MF16/Definitions.lean', 'Challenge.lean', 'reviews/statement-referee-2-evidence/Inspect.lean']:
    name = 'Definitions' if 'Definitions' in source else ('Challenge' if 'Challenge' in source else 'Inspect')
    output = prefix / Path(source).with_suffix('.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    (E / (name + '.lean.txt')).write_bytes((P / source).read_bytes())
    command = [str(L / 'bin/lean'), '-o', str(output), '-i', str(output.with_suffix('.ilean')), str(P / source)]
    started = time.monotonic()
    result = subprocess.run(command, cwd=P, env=env, capture_output=True)
    log = E / (name + '.log')
    log.write_bytes(result.stdout + result.stderr)
    row = {'source': source, 'source_sha256': sha(P / source), 'command': command, 'exit_code': result.returncode,
           'seconds': time.monotonic()-started, 'log': log.name, 'log_sha256': sha(log)}
    record['commands'].append(row)
    (E / 'fresh-checks.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(row), flush=True)
    assert result.returncode == 0, log.read_text()[:4000]
pins_ok(); frozen()
record['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
record['pins_and_frozen_bytes_rechecked_after'] = True
record['verdict'] = 'PASS: fresh statement elaboration and diagnostics only; mathematical report pending'
(E / 'fresh-checks.json').write_text(json.dumps(record, indent=2) + '\n')
print('PASS: three independent fresh statement commands', flush=True)
