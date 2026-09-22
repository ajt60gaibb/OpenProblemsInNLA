#!/usr/bin/env python3
"""Independent final referee: fresh project modules, literal frozen types, axioms."""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, tempfile, time

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent.parent
LEAN = Path('/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean')
PACKAGES = Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
BUILD = Path(tempfile.mkdtemp(prefix='nla-ie22-correctness-fresh-'))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
freeze = json.loads((PROJECT/'reviews/package-source-freeze.json').read_text())
sources = freeze['source_sha256']

def hashes(stage):
    actual = {p: sha(PROJECT/p) for p in sources}
    result = {'stage': stage, 'files': actual, 'matches': actual == sources,
              'package_freeze_sha256': sha(PROJECT/'reviews/package-source-freeze.json')}
    (HERE/f'hashes-{stage}.json').write_text(json.dumps(result, indent=2)+'\n')
    assert actual == sources, 'Frozen source mismatch'
    assert result['package_freeze_sha256'] == '2a07dedc9ca3774cd9fc5a760f421dd47f105cc257c770f401ae73513dea1226'
    return result

hashes('before')
env = dict(os.environ)
env['LEAN_PATH'] = ':'.join(map(str, [BUILD] + sorted(PACKAGES.glob('*/.lake/build/lib/lean'))))
modules = {str(p.relative_to(PROJECT)).removesuffix('.lean').replace('/', '.'): p
           for p in (PROJECT/'NLA').rglob('*.lean')}
assert len(modules) == 47
order, active = [], set()
def visit(name):
    if name in order: return
    assert name not in active, 'cyclic project import'
    active.add(name)
    for dep in re.findall(r'^import\s+(NLA\.\S+)', modules[name].read_text(), re.M):
        assert dep in modules, dep
        visit(dep)
    active.remove(name)
    order.append(name)
for name in sorted(modules): visit(name)
records = []
start = datetime.datetime.now(datetime.timezone.utc).isoformat()
for name in order:
    rel = modules[name].relative_to(PROJECT)
    out = BUILD/rel.with_suffix('.olean')
    out.parent.mkdir(parents=True, exist_ok=True)
    before = time.monotonic()
    proc = subprocess.run([str(LEAN), '-o', str(out), str(rel)], cwd=PROJECT,
                          env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    logfile = HERE/(name.replace('.', '__')+'.log')
    logfile.write_text(proc.stdout)
    records.append({'module': name, 'source_sha256': sha(modules[name]),
                    'exit_code': proc.returncode, 'seconds': time.monotonic()-before,
                    'log_sha256': sha(logfile)})
    (HERE/'build-progress.json').write_text(json.dumps(records, indent=2)+'\n')
    print(name, proc.returncode, flush=True)
    assert proc.returncode == 0, proc.stdout

# Extract only the complete signatures from the frozen Challenge. Do not import it.
challenge = (PROJECT/'Challenge.lean').read_text()
declarations = re.findall(r'^theorem\s+(\w+)\s+([\s\S]*?)\s*:=\s*by\s+sorry', challenge, re.M)
selected = json.loads((PROJECT/'comparator.json').read_text())['theorem_names']
assert ['NLA.IE22.'+name for name, _ in declarations] == selected
audit = ['import NLA.IE22.Final', 'set_option autoImplicit false',
         'noncomputable section', 'open MeasureTheory ProbabilityTheory Filter Set',
         'open scoped BigOperators ENNReal RealInnerProductSpace Topology',
         'open NLA.IE21 NLA.IE22']
for name, signature in declarations:
    depth = 0
    for pos, char in enumerate(signature):
        if char in '([{': depth += 1
        elif char in ')]}': depth -= 1
        elif char == ':' and depth == 0: break
    else: raise ValueError('No top-level result colon')
    binders, conclusion = signature[:pos].strip(), signature[pos+1:].strip()
    audit.append(f'example : ∀ {binders}, {conclusion} := @NLA.IE22.{name}')
    audit.append(f'#print axioms NLA.IE22.{name}')
audit_path = HERE/'ExactFrozenTypesAndAxioms.lean'
audit_path.write_text('\n\n'.join(audit)+'\n')
proc = subprocess.run([str(LEAN), str(audit_path)], cwd=PROJECT, env=env,
                      text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(HERE/'exact-types-and-axioms.log').write_text(proc.stdout)
assert proc.returncode == 0, proc.stdout
closures = {name: sorted(x.strip() for x in axioms.split(',')) for name, axioms in
            re.findall(r"'(NLA\.IE22\.\w+)' depends on axioms: \[([^\]]*)\]", proc.stdout)}
assert set(closures) == set(selected), closures
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert all(set(a) <= allowed for a in closures.values()), closures
hashes('after')
receipt = {'phase': 'independent local final correctness rebuild', 'reviewer': 'ie22_final_correctness',
 'ai_agent': True, 'authored_any_IE22_statement_or_proof': False, 'started_utc': start,
 'completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'fresh_build_directory': str(BUILD), 'lean': str(LEAN),
 'lean_version': subprocess.check_output([str(LEAN), '--version'], text=True).strip(),
 'cached_upstream_dependency_directory': str(PACKAGES), 'project_module_count': len(records),
 'project_modules': records, 'exact_frozen_selected_types': selected, 'transitive_axioms': closures,
 'audit_source_sha256': sha(audit_path), 'audit_log_sha256': sha(HERE/'exact-types-and-axioms.log'),
 'package_source_freeze_sha256': sha(PROJECT/'reviews/package-source-freeze.json'),
 'all_57_inputs_match_before_and_after': True,
 'authoritative_linux_verification': 'pending; not performed or approved by this local build',
 'authentic_LeanCert_wrapper': 'source inspected only; not compiled in this cached local build'}
(HERE/'build-receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
print('PASS: 47 fresh project modules, 20 full frozen types, permitted axiom closures.', flush=True)
