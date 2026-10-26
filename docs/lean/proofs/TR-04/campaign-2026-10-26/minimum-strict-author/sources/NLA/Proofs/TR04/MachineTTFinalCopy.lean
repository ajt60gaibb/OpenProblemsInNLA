import NLA.Proofs.TR04.MachineTTFinalScalar

/-! Actual candidate copy into the finite store, then index increment and loop
return. Source/output separation protects the read stream; previous candidate
slots are preserved by the literal half-open write range. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def TTCopyFinalKept (j : Fin 128) : Prop := (j.val < 21 ∨ 25 < j.val) ∧ j≠76 ∧ j≠123

theorem ttCandidateCopy_relates (s : State ttProgram) (hs : s.status=.running) :
    ttCopyEmbedding.Relates (copyLoopState s.memory (s.natural 89) (ttCandidateStoreBase s)
      (s.natural 64) 0 (s.real 5)) (ttCandidateCopyEntry s) := by
  constructor
  · rfl
  · funext i; fin_cases i; rfl
  · funext i; fin_cases i <;> rfl
  · exact (copiedMemory_zero _ _ _).symm
  · exact hs

theorem ttCandidateCopyEntry_kept (s : State ttProgram) (j : Fin 128) (hj : TTCopyFinalKept j) :
    (ttCandidateCopyEntry s).natural j=s.natural j := by
  have h21 : j≠21 := by
    intro h
    have hv := congrArg Fin.val h
    change j.val=21 at hv
    rcases hj.1 with ht | ht <;> omega
  have h22 : j≠22 := by
    intro h
    have hv := congrArg Fin.val h
    change j.val=22 at hv
    rcases hj.1 with ht | ht <;> omega
  have h23 : j≠23 := by
    intro h
    have hv := congrArg Fin.val h
    change j.val=23 at hv
    rcases hj.1 with ht | ht <;> omega
  have h24 : j≠24 := by
    intro h
    have hv := congrArg Fin.val h
    change j.val=24 at hv
    rcases hj.1 with ht | ht <;> omega
  have h25 : j≠25 := by
    intro h
    have hv := congrArg Fin.val h
    change j.val=25 at hv
    rcases hj.1 with ht | ht <;> omega
  simp only [ttCandidateCopyEntry,Function.update_of_ne h21,Function.update_of_ne h22,
    Function.update_of_ne h23,Function.update_of_ne h24,Function.update_of_ne h25,Function.update_of_ne hj.2.2]

/-- The address store+j*N is computed at347/348. All legal traces then copy
exactly N cells and return189 with the actual global index incremented once. -/
theorem ttCandidate_copy_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label=347) (hs : (trace.state offset).status=.running)
    (hz : (trace.state offset).natural 127=0)
    (hd : DisjointBlocks ((trace.state offset).natural 89) ((trace.state offset).natural 64)
      (ttCandidateStoreBase (trace.state offset)) ((trace.state offset).natural 64)) :
    let s := trace.state offset
    let time := offset+(6*s.natural 64+12)
    (trace.state time).label=189 ∧ (trace.state time).status=.running ∧
      (trace.state time).natural 76=s.natural 76+1 ∧
      (trace.state time).memory=copiedMemory s.memory (s.natural 89) (ttCandidateStoreBase s) (s.natural 64) ∧
      (∀ j : Fin 128,TTCopyFinalKept j → (trace.state time).natural j=s.natural j) ∧
      (∀ j : Fin 16,j≠5 → (trace.state time).real j=s.real j) ∧
      CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+(6*s.natural 64+12) := by
  let s := trace.state offset
  obtain ⟨he,hc0⟩ := ttScalar_finish_at ht offset 8 (ttCandidateCopyEntry s) (ttCandidate_copy_setup s hl hs hz) hs
  have hrel : ttCopyEmbedding.Relates (copyLoopState s.memory (s.natural 89) (ttCandidateStoreBase s)
      (s.natural 64) 0 (s.real 5)) (trace.state (offset+8)) := by
    rw [he]; exact ttCandidateCopy_relates s hs
  obtain ⟨value,hr,hc1⟩ := ttCopyEmbedding.copy_run_at s.memory (s.natural 89) (ttCandidateStoreBase s)
    (s.natural 64) (s.real 5) hd ht (offset+8) hrel
  let mid := offset+8+(6*s.natural 64+1)
  have hrl : (trace.state mid).label=39 := hr.label
  obtain ⟨hf,hc2⟩ := ttScalar_finish_at ht mid 3 (ttCandidateCopyReturn (trace.state mid))
    (ttCandidate_copy_return _ hrl hr.status) hr.status
  have hno := copyProgram_nohalt_prefix s.memory (s.natural 89) (ttCandidateStoreBase s) (s.natural 64) (s.real 5) hd
  have hscalar : ∀ k<6*s.natural 64+1,instructionIsSVD (copyProgram.code
      ((ordinaryStep copyProgram)^[k] (copyLoopState s.memory (s.natural 89) (ttCandidateStoreBase s)
        (s.natural 64) 0 (s.real 5))).label)=false := fun _ _ => copyProgram_scalar _
  have hn := ttCopyEmbedding.scalar_trace_natural_outside _ hrel (legalTrace_shift ht (offset+8)) _ hno hscalar
  have hreal := ttCopyEmbedding.scalar_trace_real_outside _ hrel (legalTrace_shift ht (offset+8)) _ hno hscalar
  have hnat : ∀ j : Fin 128,(j.val<21 ∨ 25<j.val) → (trace.state mid).natural j=(trace.state (offset+8)).natural j := by
    intro j hj
    apply hn j
    intro i hij
    have hval := congrArg Fin.val hij
    change j.val=21+i.val at hval
    have hi : i.val<5 := i.isLt
    omega
  have htime : mid+3=offset+(6*s.natural 64+12) := by dsimp [mid]; omega
  change (trace.state (offset+(6*s.natural 64+12))).label=189 ∧ _
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
    change (trace.state mid).real j=(trace.state (offset+8)).real j at hh
    rw [hh,he]
    rfl
  · dsimp [mid,s] at hc0 hc1 hc2 ⊢
    omega

/-- Every address outside the current slot, including every earlier candidate,
is unchanged. This does not assume an abstract candidate evaluator. -/
theorem ttCandidate_copy_earlier (memory : ℕ → ℝ) (source store entries j i k : ℕ)
    (hi : i<j) (hk : k<entries) :
    copiedMemory memory source (store+j*entries) entries (store+i*entries+k)=
      memory (store+i*entries+k) := by
  apply copiedMemory_outside
  have hh := Nat.mul_le_mul_right entries (show i+1≤j by omega)
  rw [Nat.add_mul,Nat.one_mul] at hh
  omega

theorem ttCandidate_copy_cell (memory : ℕ → ℝ) (source store entries j k : ℕ)
    (hk : k<entries) :
    copiedMemory memory source (store+j*entries) entries (store+j*entries+k)= memory (source+k) := by
  unfold copiedMemory
  rw [if_pos (by omega)]
  congr 1
  omega

#assert_trust kernel ttCandidateCopy_relates
#assert_trust kernel ttCandidateCopyEntry_kept
#assert_trust kernel ttCandidate_copy_at
#assert_trust kernel ttCandidate_copy_earlier
#assert_trust kernel ttCandidate_copy_cell
#print axioms ttCandidate_copy_at
end NLA.Proofs.TR04
