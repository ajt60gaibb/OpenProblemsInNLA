from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,datetime

p=argparse.ArgumentParser(description='Fresh source-only canonical IE-22 replay; macOS author evidence, not Linux Comparator acceptance.')
p.add_argument('--project',type=Path,required=True);p.add_argument('--lean',type=Path,required=True)
p.add_argument('--packages',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
a=p.parse_args();a.output.mkdir(parents=True,exist_ok=False)
source=a.output/'source';out=a.output/'out';logs=a.output/'logs'
source.mkdir();out.mkdir();logs.mkdir()
sources={}
for f in sorted(a.project.rglob('*.lean')):
 rel=f.relative_to(a.project)
 if '.lake' in rel.parts:continue
 assert all(not x.startswith('.') for x in rel.parts)
 module='.'.join(rel.with_suffix('').parts);data=f.read_bytes();q=source/rel;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(data)
 sources[module]={'path':str(rel),'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
assert len(sources)==27,(len(sources),list(sources))
order=[];visiting=set()
def visit(module):
 if module in order:return
 assert module not in visiting,('cycle',module)
 visiting.add(module)
 for line in (source/sources[module]['path']).read_text().splitlines():
  if line.startswith('import '):
   for dep in line[7:].split():
    if dep in sources:visit(dep)
 visiting.remove(module);order.append(module)
for module in sources:visit(module)
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out)]+[str(q/'.lake/build/lib/lean') for q in sorted(a.packages.iterdir()) if (q/'.lake/build/lib/lean').is_dir()]+[str(a.lean.parent.parent/'lib/lean')])
records=[]
def compile_one(module,relative):
 f=source/relative;obj=out/Path(*module.split('.')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 argv=[str(a.lean),'-R',str(source),'-o',str(obj),str(f)]
 run=subprocess.run(argv,cwd=source,env=env,text=True,capture_output=True,timeout=300)
 (logs/(module+'.log')).write_text(run.stdout+run.stderr)
 records.append({'module':module,'source_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'argv':argv,'exit_code':run.returncode,'stdout':run.stdout,'stderr':run.stderr})
 (a.output/'result.json').write_text(json.dumps({'scope':'Fresh author canonical source replay, not Linux/Comparator','UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'inputs':sources,'records':records},indent=2)+'\n')
 print(module,run.returncode,flush=True)
 if run.returncode: print(run.stdout+run.stderr,flush=True);raise SystemExit(run.returncode)
for module in order:compile_one(module,sources[module]['path'])
(source/'CanonicalConsumer.lean').write_text('''import Solution
import Identity

set_option autoImplicit false
set_option leancert.trust "kernel"
open NLA.Statements.RowDeletion

example : NLA.Statements.IE22.Target := NLA.Proofs.IE22.target
example : NLA.ReviewedStatements.IE22.Target := by
  rw [← NLA.Proofs.IE22.target_eq_reviewed]
  exact NLA.Proofs.IE22.target

example (θ a : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : 0 < a)
    (hq : GaussianQuantile θ a) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n m : ℕ, 0 < n → 0 < m → N ≤ n →
        ∀ A : Matrix (Fin m) (Fin n) ℝ, UnitRows A →
          (n : ℝ)/(m : ℝ)*SubsingularSquared θ A ≤ TrimmedMoment a+ε :=
  NLA.Proofs.IE22.uniform_squared_upper θ a hθ0 hθ1 ha hq

example (θ a : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : 0 < a)
    (hq : GaussianQuantile θ a) :
    ∀ ε : ℝ, 0 < ε → ∀ N R : ℕ,
      ∃ n m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℝ,
        0 < n ∧ 0 < m ∧ N ≤ n ∧ R*n ≤ m ∧ UnitRows A ∧
          TrimmedMoment a-ε ≤ (n : ℝ)/(m : ℝ)*SubsingularSquared θ A :=
  NLA.Proofs.IE22.near_sharp_unit_row_witness θ a hθ0 hθ1 ha hq

#assert_trust kernel NLA.Proofs.IE22.target
#assert_trust kernel NLA.Proofs.IE22.uniform_squared_upper
#assert_trust kernel NLA.Proofs.IE22.near_sharp_unit_row_witness
#assert_trust kernel IE22.l2Sq_zero
#assert_trust kernel IE22.rowEnergy_empty
#print axioms NLA.Proofs.IE22.target
#print axioms NLA.Proofs.IE22.uniform_squared_upper
#print axioms NLA.Proofs.IE22.near_sharp_unit_row_witness
#print axioms IE22.l2Sq_zero
#print axioms IE22.rowEnergy_empty
''')
compile_one('CanonicalConsumer','CanonicalConsumer.lean')
assert all(hashlib.sha256((a.project/v['path']).read_bytes()).hexdigest()==v['sha256'] for v in sources.values())
print('PASS:27fresh canonical sources+exact endpoints/Reviewed Target/old support consumer; no Linux claim',flush=True)
