#!/usr/bin/env python3
"""Fresh author replay of explicit radix and literal machine interfaces; no CI/Target claim."""
import argparse,hashlib,json,os,pathlib,re,subprocess,sys
HERE=pathlib.Path(__file__).resolve().parent
REPO=HERE.parents[5];LIVE=REPO/'lean-statements'
TOOLING=pathlib.Path(os.environ.get('NLA_CAMPAIGN_TOOLING',REPO.parent/'tooling'))
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=pathlib.Path,default=HERE/'run')
OUT=parser.parse_args().output.resolve();SNAP=OUT/'sources';OBJECTS=OUT/'objects'
assert not OBJECTS.exists(),'Choose a new output: project objects may not be reused.'
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lock=json.loads((HERE/'source-lock.json').read_text())
for rec in lock['project_closure']+lock['unchanged_boundary_and_pins']:
 assert digest(REPO/rec['path'])==rec['sha256'],rec['path']
for rec in lock['project_closure']:
 rel=pathlib.Path(rec['path']).relative_to('lean-statements');dst=SNAP/rel
 dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes((LIVE/rel).read_bytes())
(SNAP/'.lake').mkdir(exist_ok=True)
(SNAP/'.lake/packages').symlink_to((LIVE/'.lake/packages').resolve(),target_is_directory=True)
env=dict(os.environ,NLA_CAMPAIGN_SOURCE_ROOT=str(SNAP),NLA_CAMPAIGN_OBJECT_ROOT=str(OBJECTS))
command=[sys.executable,str(TOOLING/'tr06-build-closure.py')]+lock['targets']
with (OUT/'source-build.log').open('w') as log:
 proc=subprocess.run(command,cwd=REPO,env=env,stdout=log,stderr=subprocess.STDOUT)
assert proc.returncode==0,OUT/'source-build.log'
consumer=SNAP/'RecursiveTensorAuthorConsumer.lean'
consumer_text='''import NLA.Proofs.TR04.TensorCompressionRadixDecode
import NLA.Proofs.TR04.TTCompletionOriginal
import NLA.Proofs.TR04.TTCompletionProjected
import NLA.Proofs.TR04.TensorCompressionLinear
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace RecursiveTensorAuthorConsumer
open NLA.Computation.TensorTrainApproximation
open NLA.Proofs.TR04.TensorFormat
 theorem actual_original_completion (S : Shape) (r : Ranks S) (A : Tensor S) :
    ∃ X : Tensor S, (∀ j, Matrix.rank (Unfold S X j) ≤ r j) ∧
      FrobeniusSq S A X ≤ ((S.order - 1 : ℕ) : ℝ) *
        sInf {e : ℝ | ∃ Y : Tensor S,
          (∀ j, Matrix.rank (Unfold S Y j) ≤ r j) ∧ e = FrobeniusSq S A Y} ∧
      (Optimum S r A = 0 → X = A) := by
  obtain ⟨X, hX⟩ := original_completion_exists S r A
  exact ⟨X, original_completion_feasible hX, original_completion_optimum_bound hX,
    original_completion_exact_of_optimum_zero hX⟩
#assert_trust kernel actual_original_completion
#print axioms actual_original_completion
 theorem actual_literal_decode (S : Shape) (x : Index S) :
    Decode S (Offset S x) = x := original_decode_offset S x
 theorem actual_literal_encode (S : Shape) (address : ℕ) (h : address < DenseSize S) :
    Offset S (Decode S address) = address := original_offset_decode S address h
 theorem actual_input_cell (S : Shape) (r : Ranks S) (A : Tensor S) (x : Index S) :
    InputMemory S r A (2 * S.order - 1 + Offset S x) = A x :=
  original_inputMemory_tensor_cell S r A x
 theorem actual_SVD_right_transport {m l : ℕ} (B : Matrix (Fin m) (Fin l) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) (sigma : Fin (min m l) → ℝ)
    (V : Matrix (Fin l) (Fin l) ℝ) (e : Fin l ≃ Fin l)
    (h : NLA.Computation.SVDMachine.ValidSVD B U sigma V) :
    NLA.Computation.SVDMachine.ValidSVD (B.submatrix id e) U sigma (V.submatrix e id) :=
  validSVD_reindex_columns h e
#assert_trust kernel actual_literal_decode
#assert_trust kernel actual_literal_encode
#assert_trust kernel actual_input_cell
#assert_trust kernel actual_SVD_right_transport
#print axioms actual_literal_decode
#print axioms actual_literal_encode
#print axioms actual_input_cell
#print axioms actual_SVD_right_transport
end RecursiveTensorAuthorConsumer
'''
for name in lock['authored_declarations']:
 consumer_text+='#assert_trust kernel '+name+'\n#print axioms '+name+'\n'
consumer.write_text(consumer_text)
binary=TOOLING/'lean-4.33.1-darwin_aarch64/bin/lean'
paths=[OBJECTS]+[p/'.lake/build/lib/lean' for p in sorted((SNAP/'.lake/packages').iterdir()) if (p/'.lake/build/lib/lean').is_dir()]
cenv=dict(env,LEAN_PATH=os.pathsep.join(map(str,paths)),PATH=str(binary.parent)+os.pathsep+os.environ['PATH'])
consumer_cmd=[str(binary),'-o',str(OBJECTS/'RecursiveTensorAuthorConsumer.olean'),str(consumer)]
with (OUT/'consumer-build.log').open('w') as log:
 cp=subprocess.run(consumer_cmd,cwd=SNAP,env=cenv,stdout=log,stderr=subprocess.STDOUT)
assert cp.returncode==0,OUT/'consumer-build.log'
for rec in lock['project_closure']+lock['unchanged_boundary_and_pins']:
 assert digest(REPO/rec['path'])==rec['sha256'],rec['path']
for rec in lock['project_closure']:
 assert digest(SNAP/pathlib.Path(rec['path']).relative_to('lean-statements'))==rec['sha256']
logs=(OUT/'source-build.log').read_text()+(OUT/'consumer-build.log').read_text()
assert 'sorryAx' not in logs
axioms=re.findall(r'depends on axioms: \[([^]]*)\]',logs)
assert all(set(x.strip() for x in a.split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'} for a in axioms)
metas=sorted(OBJECTS.rglob('*.source-sha256.json'))
assert len(metas)==len(lock['project_closure'])
original_lock=json.loads((HERE.parent/'input-lock.json').read_text())['records']
assert all(digest(REPO/x['path'])==x['sha256'] for x in original_lock)
result={'author':'/root/recover_geometry','date':'2026-10-25','passed':True,
 'scope':'Fresh author kernel replay of explicit radix/Offset/Decode/input-memory and arbitrary SVD right-column transport interfaces; no independent review, strict TR04 Target, actual finite program/runtime, Linux CI or Comparator claim',
 'source_lock_sha256':digest(HERE/'source-lock.json'),'driver_sha256':digest(pathlib.Path(__file__)),
 'authored_source_count':len(lock['authored_sources']),'fresh_project_closure_source_count':len(metas),
 'fresh_kernel_command_count':len(metas)+1,'authored_declarations_asserted':len(lock['authored_declarations']),
 'literal_original_sInf_rank_error_consumer':True,'literal_Offset_Decode_InputMemory_ValidSVD_consumers':True,'project_objects_reused':False,
 'pinned_external_package_cache_reused':True,'source_build_exit_code':proc.returncode,
 'consumer_build_exit_code':cp.returncode,'all_frozen_live_and_snapshot_sources_unchanged':True,
 'all_25_original_review_inputs_preserved':True,'printed_axiom_lists':axioms,
 'compiler':subprocess.check_output([str(binary),'--version'],text=True).strip(),
 'source_command':command,'consumer_command':consumer_cmd,
 'evidence':[{'path':str(p.relative_to(OUT)),'sha256':digest(p)} for p in [consumer,OUT/'source-build.log',OUT/'consumer-build.log']]}
(OUT/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
