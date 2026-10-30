#!/usr/bin/env python3
"""Independent, source-frozen review replay. Does not edit candidate sources."""
from pathlib import Path
import hashlib, json, os, re, subprocess, tempfile, time

REPO = Path('/Users/ajt253/.codex/worktrees/re06-nonadaptive-oct26/OpenProblemsInNLA')
HERE = Path(__file__).resolve().parent
PACKET = REPO/'docs/lean/proofs/RE-06/campaign-2026-10-26/preproof'
AUTH = PACKET.parent/'IMPLEMENTATION_AUTHORIZATION.json'
INVERSE = PACKET.parent/'inverse-moment-author'
OUTER = Path('/Users/ajt253/Documents/OpenProblemsInNLA/reviews/2026-10-23-solved-lean/re06-outer-moment-author')
LEAN = Path('/private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean')
PACKAGES = Path('/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages')
BASE = '099805ef1ce7347d373e47cccc3b2d7cf580a99e'
AUTH_COMMIT = 'bb0dd13e3321bb35af762936a75c2c3a8a8363c6'
sha = lambda b: hashlib.sha256(b).hexdigest()
file_sha = lambda p: sha(p.read_bytes())
def git(*args):
    return subprocess.check_output(['git','-C',str(REPO),*args])
checks=[]
def check(label, test, **details):
    checks.append(dict(label=label, passed=bool(test), **details))
    if not test:
        raise AssertionError(label)
def dump(name, data):
    (HERE/name).write_text(json.dumps(data, indent=2)+'\n')

auth=json.loads(AUTH.read_text())
check('implementation authorization is frozen commit bytes', AUTH.read_bytes()==git('show',f'{AUTH_COMMIT}:{AUTH.relative_to(REPO)}'))
check('implementation authorized',auth['implementation_authorized'] is True)
for name, expected in auth['reviewed_packet_hashes'].items():
    check(f'frozen preproof {name}',file_sha(PACKET/name)==expected,sha256=expected)
lock=json.loads((PACKET/'INPUT_LOCK.json').read_text())
for row in lock['files']:
    live=(REPO/row['path']).read_bytes()
    original=git('show',f'{BASE}:{row["path"]}')
    snapshot=(PACKET/'originals'/row['path']).read_bytes()
    check(f'published original {row["path"]}',live==original==snapshot and sha(live)==row['sha256'],sha256=sha(live))
registry=json.loads((REPO/'problem_ids.json').read_text())
check('all 217 original ID/path pairs retained',len(registry)==217 and registry==json.loads(git('show',f'{BASE}:problem_ids.json')))
inverse_freeze=INVERSE/'SOURCE_FREEZE.json'
outer_freeze=OUTER/'SOURCE_FREEZE.json'
check('inverse freeze digest',file_sha(inverse_freeze)=='015a514807d2e1426c72116f3521fcbdac000a33a9292b066a59059e8dbf261d')
check('outer freeze digest',file_sha(outer_freeze)=='e20c9fba32e1e9b49bdad584d906b85fc206b41b9593b67505d1951f8f9ace85')
check('sealed inverse author result digest',file_sha(INVERSE/'fresh-replay/RESULT.json')=='e6a166ce569c6c880ab64b0b84810d7996247941b0fbb6d9bfd20f900dabbcb2')
check('sealed inverse author file manifest digest',file_sha(INVERSE/'FILE_SHA256.json')=='3734e4fa0b861648fb2861db24c480db926c0ad183e3c3246f1908364ef10feb')
frozen=json.loads(outer_freeze.read_text())['files']
check('outer freeze has exactly 82 inputs',len(frozen)==82)
for row in frozen:
    p=REPO/row['path']
    check(f'candidate source {row["module"]}',file_sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],sha256=row['sha256'])
for row in json.loads(inverse_freeze.read_text())['files']:
    check(f'unchanged inverse input {row["module"]}',file_sha(REPO/row['path'])==row['sha256'])
for module, expected in [
 ('GaussianMomentOuterFoundation','7a506a000636d18f3ba96a8c8906107c92471755f13901dc859dc8b04ca84cbd'),
 ('GaussianMomentOuter','6f3c9bbad9794ebb63a0fb3f2e04f44ce6f29f023039fcb9d6f0f95929457dab'),
 ('GaussianMomentOuterAudit','1a6fa5779b905a4c794313c5e0672c06f19b5172eb3d5ffc174abb99ec18a23b')]:
    check(f'explicit outer hash {module}',file_sha(REPO/f'lean-statements/NLA/Proofs/RE06/{module}.lean')==expected)
math_modules=['GaussianMoment'+x for x in ['Schur','Kernel','Row','Rows','Fubini','Inverse','Transport','OuterFoundation','Outer']]
new_names=[]
per_module={}
for mod in math_modules:
    txt=(REPO/f'lean-statements/NLA/Proofs/RE06/{mod}.lean').read_text()
    names=re.findall(r'^theorem\s+(\w+)',txt,re.M)
    per_module[mod]=names
    new_names += ['NLA.Proofs.RE06.GaussianMoment.'+x for x in names]
    check(f'kernel trust set in {mod}','set_option leancert.trust "kernel"' in txt)
    check(f'no proof escape tokens in {mod}',not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',txt))
check('54 inverse and 7 outer actual theorem declarations',sum(len(per_module[m]) for m in math_modules[:7])==54 and len(new_names)==61)
audited=[]
for mod in ['GaussianMomentInverseAudit','GaussianMomentOuterAudit']:
    txt=(REPO/f'lean-statements/NLA/Proofs/RE06/{mod}.lean').read_text()
    for directive in ['actual_theorem','assert_trust kernel','print axioms']:
        found=re.findall(r'^#'+directive+r'\s+([\w.]+)',txt,re.M)
        if directive=='actual_theorem': audited+=found
        check(f'{mod} {directive} count',len(found)==(54 if mod.endswith('InverseAudit') else 7))
check('exact 61 audit names match actual theorem declarations',new_names==audited)
version=subprocess.check_output([str(LEAN),'--version'],text=True).strip()
check('exact pinned Lean version','4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version)
manifest=json.loads((REPO/'lean-statements/lake-manifest.json').read_text())
def heads():
    out={}
    for row in manifest['packages']:
        h=subprocess.check_output(['git','-C',str(PACKAGES/row['name']),'rev-parse','HEAD'],text=True).strip()
        check(f'package pin {row["name"]}',h==row['rev'])
        out[row['name']]=h
    return out
before=heads()
dump('SOURCE_CHECKS.json',dict(reviewer='/root/re06_counts/inverse_outer_crosscheck',author=False,scope='61 inverse/outer support theorem source and mathematical review only',checks=checks,per_module_theorems=per_module,authorization_sha256=file_sha(AUTH),inverse_freeze_sha256=file_sha(inverse_freeze),outer_freeze_sha256=file_sha(outer_freeze),lean_version=version,lean_sha256=file_sha(LEAN),package_heads=before))

# Build the frozen project import graph independently from the source import lines.
module_rows={r['module']:r for r in frozen}
deps={}
for mod,row in module_rows.items():
    imports=re.findall(r'^import\s+([\w.]+)',(REPO/row['path']).read_text(),re.M)
    deps[mod]=[i for i in imports if i.startswith(('NLA.','Reviewed.'))]
    check(f'project import closure {mod}',all(i in module_rows for i in deps[mod]))
order=[]
visiting=set()
def visit(mod):
    if mod in order: return
    assert mod not in visiting,mod
    visiting.add(mod)
    for d in deps[mod]: visit(d)
    visiting.remove(mod)
    order.append(mod)
for mod in module_rows: visit(mod)
audit='import NLA.Proofs.RE06.GaussianMomentOuterAudit\nset_option autoImplicit false\nset_option leancert.trust "kernel"\n'
for name in new_names:
    audit+=f'#check {name}\n#actual_theorem {name}\n#assert_trust kernel {name}\n#print axioms {name}\n'
audit+='''
open MeasureTheory ProbabilityTheory
open NLA.Computation.NonadaptiveMatrixQuery
open NLA.Proofs.RE06
open NLA.Proofs.RE06.GaussianMoment
example (d p : ℕ) (hp : d + 1 < p) :
    Integrable (fun x : (Fin d × Fin p) → ℝ =>
      Pseudo.frobeniusSq (pseudoInverse (entryMatrix x)))
      (Measure.pi (fun _ : Fin d × Fin p => gaussianReal 0 1)) :=
  pseudoinverse_frobeniusSq_integrable d p hp
example :
    (∫ x : (Fin 0 × Fin 2) → ℝ, Pseudo.frobeniusSq (pseudoInverse (entryMatrix x))
      ∂Measure.pi (fun _ : Fin 0 × Fin 2 => gaussianReal 0 1)) = 0 := by
  simpa using pseudoinverse_frobeniusSq_integral 0 2 (by omega)
example :
    (∫ x : (Fin 1 × Fin 3) → ℝ, Pseudo.frobeniusSq (pseudoInverse (entryMatrix x))
      ∂Measure.pi (fun _ : Fin 1 × Fin 3 => gaussianReal 0 1)) = 1 := by
  norm_num at *
  simpa using pseudoinverse_frobeniusSq_integral 1 3 (by omega)
example (C : Matrix (Fin 0) (Fin 0) ℝ) :=
  actual_excess_majorant_moment (k := 2) (ell := 4) C 0 (by omega) (by omega) (by omega)
example (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) :=
  actual_excess_majorant_moment (k := n+2) (ell := n+4) C n (by omega) (by omega) (by omega)
'''
negative_sources={
 'Crosscheck.Hole':'''import NLA.Proofs.RE06.GaussianMomentOuterAudit
set_option leancert.trust "kernel"
theorem forged : True := by sorry
#assert_trust kernel forged
''',
 'Crosscheck.Alias':'''import NLA.Proofs.RE06.GaussianMomentOuterAudit
def forged := @NLA.Proofs.RE06.GaussianMoment.actual_excess_majorant_moment
#actual_theorem forged
''',
 'Crosscheck.Axiom':'''import NLA.Proofs.RE06.GaussianMomentOuterAudit
set_option leancert.trust "kernel"
axiom counterfeit : True
theorem forged : True := counterfeit
#assert_trust kernel forged
'''}
records=[]
start=time.time()
with tempfile.TemporaryDirectory(prefix='nla-independent-inverse-outer-',dir='/private/tmp') as tmp:
    tmp=Path(tmp); source=tmp/'source'; obj=tmp/'objects'; source.mkdir(); obj.mkdir()
    for mod,row in module_rows.items():
        path=source/(mod.replace('.','/')+'.lean');path.parent.mkdir(parents=True,exist_ok=True)
        data=(REPO/row['path']).read_bytes();path.write_bytes(data)
        dest=HERE/'sources'/(mod.replace('.','/')+'.lean.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
    for mod,body in dict({'Crosscheck.Audit':audit},**negative_sources).items():
        path=source/(mod.replace('.','/')+'.lean');path.parent.mkdir(parents=True,exist_ok=True);path.write_text(body)
        dest=HERE/'sources'/(mod.replace('.','/')+'.lean.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(body)
    env=os.environ.copy()
    env['LEAN_PATH']=':'.join([str(obj)]+[str(p/'.lake/build/lib/lean') for p in sorted(PACKAGES.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]+[str(LEAN.parent.parent/'lib/lean')])
    for mod in order+['Crosscheck.Audit']+list(negative_sources):
        src=source/(mod.replace('.','/')+'.lean'); dst=obj/(mod.replace('.','/')+'.olean');dst.parent.mkdir(parents=True,exist_ok=True)
        argv=[str(LEAN),'-R',str(source),'-o',str(dst),str(src)]
        proc=subprocess.run(argv,cwd=source,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=600)
        log=proc.stdout
        if mod=='Crosscheck.Hole': ok=proc.returncode!=0 and 'sorryAx' in log and 'error: #assert_trust:' in log
        elif mod=='Crosscheck.Alias': ok=proc.returncode!=0 and 'expected actual theorem declaration' in log and 'unknown identifier' not in log.lower()
        elif mod=='Crosscheck.Axiom': ok=proc.returncode!=0 and 'counterfeit' in log and 'error: #assert_trust:' in log
        else: ok=proc.returncode==0
        (HERE/(mod+'.log')).write_text(log)
        axioms=re.findall(r"depends on axioms:\s*\[([^\]]*)\]",log)
        axiom_names=sorted({a.strip() for s in axioms for a in s.split(',') if a.strip()})
        if mod=='Crosscheck.Audit': ok=ok and set(axiom_names)<= {'propext','Classical.choice','Quot.sound'} and len(axioms)==61
        records.append(dict(module=mod,argv=argv,source_sha256=file_sha(src),exit_code=proc.returncode,negative=mod in negative_sources,passed=ok,warnings=log.count('warning:'),axioms=axiom_names))
        dump('PROGRESS.json',dict(records=records,elapsed_seconds=time.time()-start))
        print(f'{len(records)}/86 {mod}: {"PASS" if ok else "FAIL"}',flush=True)
        if not ok: print(log,flush=True);break
after=heads()
check('external package heads unchanged',before==after)
for row in frozen:
    check(f'after replay source {row["module"]}',file_sha(REPO/row['path'])==row['sha256'])
result=dict(reviewer='/root/re06_counts/inverse_outer_crosscheck',independent_of_author=True,scope='Exact frozen 61 inverse/outer support theorem declarations only; no whole RE06/public Target/CI/Comparator approval',passed=len(records)==86 and all(r['passed'] for r in records),fresh_project_objects=True,project_objects_removed_after_replay=True,project_object_source='Only this replay temporary objects; no shared project object search path',external_packages=before,lean_version=version,lean_sha256=file_sha(LEAN),source_freeze_sha256=file_sha(outer_freeze),records=records,checks=checks,elapsed_seconds=time.time()-start)
dump('RESULT.json',result)
raise SystemExit(0 if result['passed'] else 1)
