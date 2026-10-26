#!/usr/bin/env python3
"""Independent other-author assembly replay and literal original-target consumers.
Own algebra/radial prerequisites are expressly outside independent authorship review.
Unselected previously-built project prerequisites are source/hash-bound, not called fresh builds.
"""
import hashlib,json,os,platform,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[5];ROOT=REPO/'lean-statements'
LEAN=REPO.parent/'tooling/lean-4.33.1-darwin_aarch64/bin/lean'
SHARED=ROOT/'.lake/build/lib/lean'
SOURCES=HERE/'sources';OBJECTS=HERE/'objects'
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
selected={
 'NLA.Statements.Infrastructure','NLA.Statements.TR06','Reviewed.TR06',
 *['NLA.Proofs.TR06.'+name for name in [
 'ControlledProjectionAtlas','ControlledProjectionDerivative','NormalizedGraphEuclidean',
 'NormalizedGraphRows','NormalizedGraphParameter','NormalizedGraphQuasiFiniteRows',
 'NormalizedGraphQuasiFiniteControlled','FiniteUnionFiberBounds','ControlledProjectionVolume',
 'NormalizedGraphBounded','NormalizedGraphFiniteFibers','NormalizedGraphFiniteVolume','Final',
 'RetainedBoundaryLocus','RetainedBoundaryMean']]}
seen=set();order=[]
def visit(module):
 if module in seen:return
 path=ROOT/(module.replace('.','/')+'.lean');assert path.exists(),module;seen.add(module)
 for dep in re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',path.read_text(),re.M):
  if dep.startswith(('NLA.','Reviewed.')):visit(dep)
 order.append(module)
visit('NLA.Proofs.TR06.RetainedBoundaryMean');visit('Reviewed.TR06')
SOURCES.mkdir(exist_ok=True);OBJECTS.mkdir(exist_ok=True)
assert not list(OBJECTS.rglob('*.olean')),'Fresh private selected-source output is required.'
locks=[];prerequisites=[]
for module in order:
 rel=Path(module.replace('.','/')+'.lean');path=ROOT/rel;sha=digest(path)
 record={'module':module,'path':'lean-statements/'+str(rel),'sha256':sha}
 if module not in selected:
  obj=SHARED/rel.with_suffix('.olean');meta=obj.with_suffix('.source-sha256.json')
  if not obj.exists() or not meta.exists() or json.loads(meta.read_text()).get('sha256')!=sha:
   selected.add(module);record['reason_for_additional_fresh_replay']='Shared source/object binding absent or stale'
  else:prerequisites.append({**record,'object_sha256':digest(obj),'source_binding_metadata_sha256':digest(meta)})
 if module in selected:
  out=SOURCES/rel;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(path.read_bytes())
 locks.append(record)
(HERE/'closure-source-lock.json').write_text(json.dumps(locks,indent=2)+'\n')
(HERE/'read-only-prerequisite-bindings.json').write_text(json.dumps(prerequisites,indent=2)+'\n')
# Lean resolves a project namespace from one root; use an explicit read-only
# per-file view for unchanged prerequisites, rather than relying on fallback.
for item in prerequisites:
 rel=Path(item['path']).relative_to('lean-statements').with_suffix('.olean')
 link=OBJECTS/rel;link.parent.mkdir(parents=True,exist_ok=True)
 assert not link.exists()
 link.symlink_to((SHARED/rel).resolve())

old=REPO/'docs/lean/proofs/TR-06/campaign-2026-10-18/published-partial-boundary/Challenge.lean'
original=old.read_text()
headers=re.findall(r'^theorem\s+(\w+)(.*?) := by\n  sorry',original,re.M|re.S)
assert len(headers)==10
args={
 'derivativeRatio_eq_operatorNorm':'dφ dg hinj',
 'angularSlope_eq_chart_derivative':'c u hu',
 'induced_volume_chart':'c s hs hsub',
 'regular_locus':'n r hd hn hr hgeneric',
 'finite_angular_mean':'n r hd hn hr hgeneric',
 'generic_iff_source':'d n r',
 'smooth_locus_correspondence':'n r hd hn hr hgeneric',
 'smooth_chart_is_local_addition_inverse':'hd hn hr c u hu',
 'source_model_correspondence':'n r hd hn hr hgeneric',
 'finite_angular_mean_source':'n r hd hn hr hgeneric'}
consumer='''/- Original ten specification headers: copyright 2026 George Stepaniants, Apache-2.0.
Regenerated independently from the preserved published Challenge; no Challenge import. -/
import NLA.Proofs.TR06.RetainedBoundaryMean
import Reviewed.TR06
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal MeasureTheory
open MeasureTheory Set
namespace NLA.TR06
'''
for name,header in headers:
 new='independent_original_'+name
 consumer+='\ntheorem '+new+header+' := by\n  exact NLA.TR06.'+name+' '+args[name]+'\n'
 consumer+='#assert_trust kernel '+new+'\n#print axioms '+new+'\n'
consumer+='''
end NLA.TR06
namespace IndependentTR06Assembly
/-- Literal original quantifiers, true normalizer and true intrinsic numerator. -/
theorem intrinsic_literal :
    ∀ (d : ℕ) (dims : Fin d → ℕ) (r : ℕ),
      3 ≤ d → (∀ j : Fin d, 2 ≤ dims j) → 3 ≤ r →
      NLA.Statements.TR06.GenericComplexIdentifiable dims r →
      0 < NLA.Statements.TR06.Normalizer dims r ∧
      NLA.Statements.TR06.Normalizer dims r < ⊤ ∧
      NLA.Statements.TR06.AngularIntegral dims r /
        NLA.Statements.TR06.Normalizer dims r < ⊤ := by
  exact NLA.Proofs.TR06.target

theorem separately_reviewed_literal : NLA.ReviewedStatements.TR06.Target := by
  exact NLA.Proofs.TR06.target

#assert_trust kernel intrinsic_literal
#assert_trust kernel separately_reviewed_literal
#print axioms intrinsic_literal
#print axioms separately_reviewed_literal
end IndependentTR06Assembly
'''
(SOURCES/'IndependentFinalConsumer.lean').write_text(consumer)
(HERE/'consumer-provenance.json').write_text(json.dumps({'original_challenge_path':str(old.relative_to(REPO)),'original_challenge_sha256':digest(old),'original_verbatim_header_count':10,'changes':'Only declaration names and proof bodies are replaced; the two extra theorems separately restate the literal intrinsic target and reviewed target. No Challenge import.','consumer_sha256':digest(SOURCES/'IndependentFinalConsumer.lean')},indent=2)+'\n')
packages=ROOT/'.lake/packages'
paths=[OBJECTS]+[p/'.lake/build/lib/lean'for p in sorted(packages.iterdir())if(p/'.lake/build/lib/lean').is_dir()]
env=dict(os.environ,PATH=str(LEAN.parent)+os.pathsep+os.environ['PATH'],LEAN_PATH=os.pathsep.join(map(str,paths)))
commands=[]
for module in [m for m in order if m in selected]+['IndependentFinalConsumer']:
 rel=Path(module.replace('.','/')+'.lean')
 out=OBJECTS/rel.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 p=subprocess.run([str(LEAN),'-o',str(out),str(rel)],cwd=SOURCES,env=env,text=True,capture_output=True)
 log=HERE/(module.split('.')[-1]+'.log');log.write_text(p.stdout+p.stderr)
 commands.append({'module':module,'source_sha256':digest(SOURCES/rel),'exit_code':p.returncode,'log_sha256':digest(log)})
 print(module,p.returncode,flush=True)
 if p.returncode:print(p.stdout+p.stderr);break
for item in locks:assert digest(REPO/item['path'])==item['sha256'],item['path']
for item in prerequisites:
 rel=Path(item['path']).relative_to('lean-statements').with_suffix('.olean')
 assert digest(SHARED/rel)==item['object_sha256'],item['path']
status='PASS'if len(commands)==len(selected)+1 and all(x['exit_code']==0 for x in commands)else'FAIL'
result={'status':status,'scope':'Independent source review/replay of other-author final assembly, with fresh literal intrinsic/reviewed Target and original ten-header consumers. Own algebra/radial prerequisites excluded from independent authorship review; unselected shared dependencies are explicitly source/object bound and not called fresh. No Linux CI or Comparator claim.','project_closure_sources':len(locks),'unselected_prerequisite_object_mode':'Individual read-only symlinks, each bound to source metadata and object hash before/after execution','fresh_selected_source_count':len(selected),'fresh_compiler_command_count':len(commands),'original_header_consumers':10,'literal_target_consumers':2,'sources':locks,'commands':commands,'lean_version':subprocess.check_output([str(LEAN),'--version'],text=True).strip(),'platform':platform.platform()}
(HERE/'result.json').write_text(json.dumps(result,indent=2)+'\n')
raise SystemExit(0 if status=='PASS'else 1)
