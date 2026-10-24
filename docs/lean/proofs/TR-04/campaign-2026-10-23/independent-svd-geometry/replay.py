#!/usr/bin/env python3
"""Independent reviewer fresh replay of exact SVD construction and literal machine endpoint."""
import argparse,hashlib,json,os,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent
REPO=HERE.parents[5]
SOURCE=REPO/'lean-statements'
TOOLING=pathlib.Path(os.environ.get('NLA_CAMPAIGN_TOOLING',REPO.parent/'tooling'))
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=pathlib.Path,default=HERE/'run')
OUT=parser.parse_args().output.resolve()
assert not (OUT/'objects').exists(),'Choose a fresh output; no project object reuse permitted.'
SNAPSHOT=OUT/'sources';OBJECTS=OUT/'objects';OUT.mkdir(parents=True,exist_ok=True)
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
authorlock=HERE.parent/'svd-totality-author/source-lock.json'
assert digest(authorlock)=='c692f19bd533916879956a4a38803db7ae26ea7ba6b9f9a32d288eac0c987d90'
lock=json.loads(authorlock.read_text())['sources']
for rec in lock:
 p=SOURCE/rec['path'];assert digest(p)==rec['sha256']
 dest=SNAPSHOT/rec['path'];dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.read_bytes())
consumer=SNAPSHOT/'IndependentConsumer.lean'
consumer.write_text('''import NLA.Proofs.TR04.SVDTotal
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace IndependentTR04SVDGeometry
open NLA.Computation.SVDMachine
 theorem literal_machine_SVD_total :
    ∀ (m l : ℕ) (B : Matrix (Fin m) (Fin l) ℝ),
      ∃ (U : Matrix (Fin m) (Fin m) ℝ) (sigma : Fin (min m l) → ℝ)
        (V : Matrix (Fin l) (Fin l) ℝ), ValidSVD B U sigma V := by
  intro m l B
  exact NLA.Proofs.TR04.SVD.exists_validSVD B
#assert_trust kernel literal_machine_SVD_total
#print axioms literal_machine_SVD_total
#assert_trust kernel NLA.Proofs.TR04.SVD.rightBasis
#assert_trust kernel NLA.Proofs.TR04.SVD.norm_image_rightBasis
#assert_trust kernel NLA.Proofs.TR04.SVD.inner_image_rightBasis
#assert_trust kernel NLA.Proofs.TR04.SVD.image_rightBasis_eq_zero
#assert_trust kernel NLA.Proofs.TR04.SVD.range_finrank_le_domain
#assert_trust kernel NLA.Proofs.TR04.SVD.range_finrank_le_codomain
#assert_trust kernel NLA.Proofs.TR04.SVD.leftVector
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormal_leftVector_positive
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_leftBasis
#assert_trust kernel NLA.Proofs.TR04.SVD.image_rightBasis_eq_smul
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_fin_truncate
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_validSVD
end IndependentTR04SVDGeometry
''')
binary=TOOLING/'lean-4.33.1-darwin_aarch64/bin/lean'
cache=SOURCE/'.lake/packages'
paths=[OBJECTS]+[p/'.lake/build/lib/lean' for p in sorted(cache.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]
env=dict(os.environ,PATH=str(binary.parent)+os.pathsep+os.environ['PATH'],LEAN_PATH=os.pathsep.join(map(str,paths)))
commands=[]
with (OUT/'build.log').open('w') as log:
 for relative in [x['path'] for x in lock]+['IndependentConsumer.lean']:
  p=SNAPSHOT/relative;dst=OBJECTS/pathlib.Path(relative).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
  cmd=[str(binary),'-o',str(dst),str(p)]
  proc=subprocess.run(cmd,cwd=SNAPSHOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  log.write(relative+'\n'+proc.stdout+'EXIT_STATUS='+str(proc.returncode)+'\n');log.flush()
  commands.append({'source':relative,'sha256':digest(p),'command':cmd,'exit_code':proc.returncode,'output':proc.stdout})
  assert proc.returncode==0,relative
for rec in lock:assert digest(SOURCE/rec['path'])==digest(SNAPSHOT/rec['path'])==rec['sha256']
axioms=re.findall(r'depends on axioms: \[([^]]*)\]',(OUT/'build.log').read_text())
assert len(axioms)==3
assert all(set(x.strip() for x in a.split(','))=={'propext','Classical.choice','Quot.sound'} for a in axioms)
result={'reviewer':'/root/recover_geometry','date':'2026-10-23','passed':True,'scope':'Independent full source review and fresh kernel replay of other-author SVDCore/SVDTotal plus literal ValidSVD endpoint; no complete TR04 algorithm/Target or Linux/Comparator claim','reviewer_authored_selected_SVD_sources':False,'source_lock_sha256':digest(authorlock),'source_records':lock,'fresh_project_source_count':3,'fresh_kernel_commands_including_consumer':4,'project_object_reuse':False,'pinned_external_dependency_cache_reuse':True,'consumer_sha256':digest(consumer),'driver_sha256':digest(pathlib.Path(__file__)),'compiler':subprocess.check_output([str(binary),'--version'],text=True).strip(),'printed_axiom_lists':axioms,'frozen_sources_unchanged':True,'commands':commands}
(OUT/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
