import NLA.Proofs.TR04.MachineTTFinalOriginal

/-! Direct continuation at the frozen reverse endpoint349. The reverse caller
has already computed store+j*N at347/348; no instruction is re-executed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
private theorem code349 : ttProgram.code 349 = .copyNat 21 127 350 := rfl
private theorem code350 : ttProgram.code 350 = .copyNat 22 64 351 := rfl
private theorem code351 : ttProgram.code 351 = .copyNat 23 89 352 := rfl
private theorem code352 : ttProgram.code 352 = .copyNat 24 123 353 := rfl
private theorem code353 : ttProgram.code 353 = .copyNat 25 123 354 := rfl
private theorem code354 : ttProgram.code 354 = .jump 33 := rfl

theorem ttCandidate_copy_setup349 (s : State ttProgram) (hl : s.label=349)
    (hs : s.status=.running) (hz : s.natural 127=0)
    (hptr : s.natural 123=ttCandidateStoreBase s) :
    (ordinaryStep ttProgram)^[6] s=ttCandidateCopyEntry s := by
  have hu : Function.update s.natural 123 (ttCandidateStoreBase s)=s.natural := by
    rw [← hptr]
    simp only [Function.update_eq_self]
  apply machineState_ext
  all_goals simp (disch := decide) only [Function.iterate_zero_apply,Function.iterate_succ_apply',
    ordinaryStep,Function.update_apply,if_neg,hl,hs,hz,hptr,
    code349,code350,code351,code352,code353,code354,ttCandidateCopyEntry,hu]

theorem ttCandidate_copy349_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label=349) (hs : (trace.state offset).status=.running)
    (hz : (trace.state offset).natural 127=0)
    (hptr : (trace.state offset).natural 123=ttCandidateStoreBase (trace.state offset))
    (hd : DisjointBlocks ((trace.state offset).natural 89) ((trace.state offset).natural 64)
      (ttCandidateStoreBase (trace.state offset)) ((trace.state offset).natural 64)) :
    let s := trace.state offset
    let time := offset+(6*s.natural 64+10)
    (trace.state time).label=189 ∧ (trace.state time).status=.running ∧
      (trace.state time).natural 76=s.natural 76+1 ∧
      (trace.state time).memory=copiedMemory s.memory (s.natural 89) (ttCandidateStoreBase s) (s.natural 64) ∧
      (∀ j : Fin 128,TTCopyFinalKept j → (trace.state time).natural j=s.natural j) ∧
      (∀ j : Fin 16,j≠5 → (trace.state time).real j=s.real j) ∧
      CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+(6*s.natural 64+10) := by
  let s := trace.state offset
  obtain ⟨he,hc0⟩ := ttScalar_finish_at ht offset 6 (ttCandidateCopyEntry s) (ttCandidate_copy_setup349 s hl hs hz hptr) hs
  have hrel : ttCopyEmbedding.Relates (copyLoopState s.memory (s.natural 89) (ttCandidateStoreBase s)
      (s.natural 64) 0 (s.real 5)) (trace.state (offset+6)) := by
    rw [he]; exact ttCandidateCopy_relates s hs
  obtain ⟨value,hr,hc1⟩ := ttCopyEmbedding.copy_run_at s.memory (s.natural 89) (ttCandidateStoreBase s)
    (s.natural 64) (s.real 5) hd ht (offset+6) hrel
  let mid := offset+6+(6*s.natural 64+1)
  have hrl : (trace.state mid).label=39 := hr.label
  obtain ⟨hf,hc2⟩ := ttScalar_finish_at ht mid 3 (ttCandidateCopyReturn (trace.state mid))
    (ttCandidate_copy_return _ hrl hr.status) hr.status
  have hno := copyProgram_nohalt_prefix s.memory (s.natural 89) (ttCandidateStoreBase s) (s.natural 64) (s.real 5) hd
  have hscalar : ∀ k<6*s.natural 64+1,instructionIsSVD (copyProgram.code
      ((ordinaryStep copyProgram)^[k] (copyLoopState s.memory (s.natural 89) (ttCandidateStoreBase s)
        (s.natural 64) 0 (s.real 5))).label)=false := fun _ _ => copyProgram_scalar _
  have hn := ttCopyEmbedding.scalar_trace_natural_outside _ hrel (legalTrace_shift ht (offset+6)) _ hno hscalar
  have hreal := ttCopyEmbedding.scalar_trace_real_outside _ hrel (legalTrace_shift ht (offset+6)) _ hno hscalar
  have hnat : ∀ j : Fin 128,(j.val<21 ∨ 25<j.val) → (trace.state mid).natural j=(trace.state (offset+6)).natural j := by
    intro j hj
    apply hn j
    intro i hij
    have hval := congrArg Fin.val hij
    change j.val=21+i.val at hval
    have hi : i.val<5 := i.isLt
    omega
  have htime : mid+3=offset+(6*s.natural 64+10) := by dsimp [mid]; omega
  change (trace.state (offset+(6*s.natural 64+10))).label=189 ∧ _
  rw [← htime,hf]
  refine ⟨rfl,hr.status,?_,hr.memory,?_,?_,?_⟩
  · change (trace.state mid).natural 76+1=s.natural 76+1
    rw [hnat 76 (by decide),he]
    rfl
  · intro j hj
    change Function.update (trace.state mid).natural 76 ((trace.state mid).natural 76+1) j=s.natural j
    rw [Function.update_of_ne hj.2.1,hnat j hj.1,he]
    exact ttCandidateCopyEntry_kept s j hj
  · intro j hj
    change (trace.state mid).real j=s.real j
    have hh := hreal j (by intro i; fin_cases i; exact hj)
    change (trace.state mid).real j=(trace.state (offset+6)).real j at hh
    rw [hh,he]
    rfl
  · dsimp [mid,s] at hc0 hc1 hc2 ⊢
    omega

theorem ttCandidate_copy349_original_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (S : Shape) (r : Ranks S) (B : Tensor S)
    (hl : (trace.state offset).label=349) (hs : (trace.state offset).status=.running)
    (hz : (trace.state offset).natural 127=0)
    (hptr : (trace.state offset).natural 123=ttCandidateStoreBase (trace.state offset)) (hN : (trace.state offset).natural 64=DenseSize S)
    (hd : DisjointBlocks ((trace.state offset).natural 89) ((trace.state offset).natural 64)
      (ttCandidateStoreBase (trace.state offset)) ((trace.state offset).natural 64))
    (hB : ∀ x,(trace.state offset).memory ((trace.state offset).natural 89+Offset S x)=B x) :
    let s := trace.state offset
    let time := offset+(6*DenseSize S+10)
    (trace.state time).label=189 ∧ (trace.state time).status=.running ∧
      (trace.state time).natural 76=s.natural 76+1 ∧
      (∀ x,(trace.state time).memory (s.natural 71+s.natural 76*DenseSize S+Offset S x)=B x) ∧
      (∀ i<s.natural 76,∀ k<DenseSize S,
        (trace.state time).memory (s.natural 71+i*DenseSize S+k)=s.memory (s.natural 71+i*DenseSize S+k)) ∧
      (∀ a,a<s.natural 71 → (trace.state time).memory a=s.memory a) ∧
      (∀ j : Fin 128,TTCopyFinalKept j → (trace.state time).natural j=s.natural j) ∧
      CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+18*(Size S r+1) := by
  obtain ⟨hl',hs',hj,hm,hn,_,hc⟩ := ttCandidate_copy349_at ht offset hl hs hz hptr hd
  simp only [hN] at hl' hs' hj hm hn hc
  refine ⟨hl',hs',hj,?_,?_,?_,hn,?_⟩
  · intro x
    rw [hm]
    change copiedMemory (trace.state offset).memory ((trace.state offset).natural 89)
      ((trace.state offset).natural 71+(trace.state offset).natural 76*(trace.state offset).natural 64)
      (DenseSize S) _=B x
    rw [hN]
    exact ttCandidate_copy_original_cells S _ _ _ _ B hB x
  · intro i hi k hk
    rw [hm]
    unfold ttCandidateStoreBase
    rw [hN]
    exact ttCandidate_copy_earlier _ _ _ _ _ i k hi hk
  · intro a ha
    rw [hm]
    unfold ttCandidateStoreBase
    rw [hN]
    exact ttCandidate_copy_before_store _ _ _ _ _ a ha
  · have hsize := shape_denseSize_le_size S r
    omega

#assert_trust kernel ttCandidate_copy_setup349
#assert_trust kernel ttCandidate_copy349_at
#assert_trust kernel ttCandidate_copy349_original_at
#print axioms ttCandidate_copy349_at
#print axioms ttCandidate_copy349_original_at
end NLA.Proofs.TR04
