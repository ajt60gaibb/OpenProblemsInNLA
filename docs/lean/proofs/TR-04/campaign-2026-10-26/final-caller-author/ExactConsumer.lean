import NLA.Proofs.TR04.MachineTTFinalOriginal
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
open NLA.Proofs.TR04 NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
namespace FinalCallerExactConsumer
theorem literal_ttCandidate_copy_at {start : State ttProgram} {trace : Trace ttProgram}
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
  exact ttCandidate_copy_at ht offset hl hs hz hd
#assert_trust kernel literal_ttCandidate_copy_at
#print axioms literal_ttCandidate_copy_at

theorem literal_ttCandidate_copy_original_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (S : Shape) (r : Ranks S) (B : Tensor S)
    (hl : (trace.state offset).label=347) (hs : (trace.state offset).status=.running)
    (hz : (trace.state offset).natural 127=0) (hN : (trace.state offset).natural 64=DenseSize S)
    (hd : DisjointBlocks ((trace.state offset).natural 89) ((trace.state offset).natural 64)
      (ttCandidateStoreBase (trace.state offset)) ((trace.state offset).natural 64))
    (hB : ∀ x,(trace.state offset).memory ((trace.state offset).natural 89+Offset S x)=B x) :
    let s := trace.state offset
    let time := offset+(6*DenseSize S+12)
    (trace.state time).label=189 ∧ (trace.state time).status=.running ∧
      (trace.state time).natural 76=s.natural 76+1 ∧
      (∀ x,(trace.state time).memory (s.natural 71+s.natural 76*DenseSize S+Offset S x)=B x) ∧
      (∀ i<s.natural 76,∀ k<DenseSize S,
        (trace.state time).memory (s.natural 71+i*DenseSize S+k)=s.memory (s.natural 71+i*DenseSize S+k)) ∧
      (∀ a,a<s.natural 71 → (trace.state time).memory a=s.memory a) ∧
      (∀ j : Fin 128,TTCopyFinalKept j → (trace.state time).natural j=s.natural j) ∧
      CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+18*(Size S r+1) := by
  exact ttCandidate_copy_original_at ht offset S r B hl hs hz hN hd hB
#assert_trust kernel literal_ttCandidate_copy_original_at
#print axioms literal_ttCandidate_copy_original_at

theorem literal_ttBest_halt_minimum_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label=189) (hs : (trace.state offset).status=.running)
    (hz : (trace.state offset).natural 127=0)
    (hp : 0<(trace.state offset).natural 75)
    (hfull : (trace.state offset).natural 75≤(trace.state offset).natural 76) :
    let s := trace.state offset
    let time := offset+(bestCandidateReturnTime (ttBestData s)+17)
    ∃ winner < s.natural 75,
      (trace.state time).status=.halted (s.natural 71+winner*s.natural 64) ∧
      (trace.state time).natural 83=s.natural 71+winner*s.natural 64 ∧
      (trace.state time).natural 54=winner ∧
      (trace.state time).real 12=(ttBestData s).candidateError winner ∧
      (∀ i<s.natural 75,(ttBestData s).candidateError winner≤(ttBestData s).candidateError i) ∧
      (trace.state time).memory=s.memory ∧
      (∀ j : Fin 128,TTBestFinalKept j → (trace.state time).natural j=s.natural j) ∧
      (∀ j : Fin 16,(j.val<9 ∨ 12<j.val) → (trace.state time).real j=s.real j) ∧
      CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+
        67*(s.natural 75+s.natural 64+1)^2 := by
  exact ttBest_halt_minimum_at ht offset hl hs hz hp hfull
#assert_trust kernel literal_ttBest_halt_minimum_at
#print axioms literal_ttBest_halt_minimum_at

theorem literal_ttBest_halt_original_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (S : Shape) (r : Ranks S)
    (A : Tensor S) (C : ℕ → Tensor S)
    (hl : (trace.state offset).label=189) (hs : (trace.state offset).status=.running)
    (hz : (trace.state offset).natural 127=0)
    (hp : 0<(trace.state offset).natural 75)
    (hfull : (trace.state offset).natural 75≤(trace.state offset).natural 76)
    (hK : (trace.state offset).natural 75≤DenseSize S)
    (hN : (trace.state offset).natural 64=DenseSize S)
    (hA : ∀ x,(trace.state offset).memory ((trace.state offset).natural 92+Offset S x)=A x)
    (hC : ∀ i<(trace.state offset).natural 75,∀ x,
      (trace.state offset).memory ((trace.state offset).natural 71+i*DenseSize S+Offset S x)=C i x) :
    let s := trace.state offset
    let time := offset+(bestCandidateReturnTime (ttBestData s)+17)
    ∃ winner<s.natural 75,
      (trace.state time).status=.halted (s.natural 71+winner*DenseSize S) ∧
      (trace.state time).natural 83=s.natural 71+winner*DenseSize S ∧
      (trace.state time).natural 54=winner ∧
      (trace.state time).real 12=FrobeniusSq S A (C winner) ∧
      (∀ i<s.natural 75,FrobeniusSq S A (C winner)≤FrobeniusSq S A (C i)) ∧
      (trace.state time).memory=s.memory ∧
      (∀ x,(trace.state time).memory (s.natural 71+winner*DenseSize S+Offset S x)=C winner x) ∧
      CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+300*(Size S r+1)^2 := by
  exact ttBest_halt_original_at ht offset S r A C hl hs hz hp hfull hK hN hA hC
#assert_trust kernel literal_ttBest_halt_original_at
#print axioms literal_ttBest_halt_original_at

theorem literal_store_index_multiplication : ttProgram.code 347 = .mulNat 123 76 64 348 := rfl
#assert_trust kernel literal_store_index_multiplication
#print axioms literal_store_index_multiplication

theorem literal_actual_candidate_increment : ttProgram.code 355 = .increment 76 356 := rfl
#assert_trust kernel literal_actual_candidate_increment
#print axioms literal_actual_candidate_increment

theorem literal_selected_output_copy : ttProgram.code 114 = .copyNat 83 55 371 := rfl
#assert_trust kernel literal_selected_output_copy
#print axioms literal_selected_output_copy

theorem literal_actual_halt : ttProgram.code 371 = .halt 83 := rfl
#assert_trust kernel literal_actual_halt
#print axioms literal_actual_halt

theorem literal_empty_copy (memory : ℕ → ℝ) (source store j : ℕ) :
    copiedMemory memory source (store+j*0) 0=memory := copiedMemory_zero _ _ _
#assert_trust kernel literal_empty_copy
#print axioms literal_empty_copy
end FinalCallerExactConsumer

#assert_trust kernel NLA.Proofs.TR04.ttCandidateStoreBase
#print axioms NLA.Proofs.TR04.ttCandidateStoreBase

#assert_trust kernel NLA.Proofs.TR04.ttCandidateCopyEntry
#print axioms NLA.Proofs.TR04.ttCandidateCopyEntry

#assert_trust kernel NLA.Proofs.TR04.ttCandidateCopyReturn
#print axioms NLA.Proofs.TR04.ttCandidateCopyReturn

#assert_trust kernel NLA.Proofs.TR04.ttBestSetupNatural
#print axioms NLA.Proofs.TR04.ttBestSetupNatural

#assert_trust kernel NLA.Proofs.TR04.ttBestEntry
#print axioms NLA.Proofs.TR04.ttBestEntry

#assert_trust kernel NLA.Proofs.TR04.ttBestHaltEnd
#print axioms NLA.Proofs.TR04.ttBestHaltEnd

#assert_trust kernel NLA.Proofs.TR04.ttCandidate_copy_setup
#print axioms NLA.Proofs.TR04.ttCandidate_copy_setup

#assert_trust kernel NLA.Proofs.TR04.ttCandidate_copy_return
#print axioms NLA.Proofs.TR04.ttCandidate_copy_return

#assert_trust kernel NLA.Proofs.TR04.ttBest_setup
#print axioms NLA.Proofs.TR04.ttBest_setup

#assert_trust kernel NLA.Proofs.TR04.ttBest_final_branch
#print axioms NLA.Proofs.TR04.ttBest_final_branch

#assert_trust kernel NLA.Proofs.TR04.ttBest_halt_steps
#print axioms NLA.Proofs.TR04.ttBest_halt_steps

#assert_trust kernel NLA.Proofs.TR04.ttBest_halt_at
#print axioms NLA.Proofs.TR04.ttBest_halt_at

#assert_trust kernel NLA.Proofs.TR04.TTCopyFinalKept
#print axioms NLA.Proofs.TR04.TTCopyFinalKept

#assert_trust kernel NLA.Proofs.TR04.ttCandidateCopy_relates
#print axioms NLA.Proofs.TR04.ttCandidateCopy_relates

#assert_trust kernel NLA.Proofs.TR04.ttCandidateCopyEntry_kept
#print axioms NLA.Proofs.TR04.ttCandidateCopyEntry_kept

#assert_trust kernel NLA.Proofs.TR04.ttCandidate_copy_at
#print axioms NLA.Proofs.TR04.ttCandidate_copy_at

#assert_trust kernel NLA.Proofs.TR04.ttCandidate_copy_earlier
#print axioms NLA.Proofs.TR04.ttCandidate_copy_earlier

#assert_trust kernel NLA.Proofs.TR04.ttCandidate_copy_cell
#print axioms NLA.Proofs.TR04.ttCandidate_copy_cell

#assert_trust kernel NLA.Proofs.TR04.ttBestData
#print axioms NLA.Proofs.TR04.ttBestData

#assert_trust kernel NLA.Proofs.TR04.ttBestScratch
#print axioms NLA.Proofs.TR04.ttBestScratch

#assert_trust kernel NLA.Proofs.TR04.TTBestFinalKept
#print axioms NLA.Proofs.TR04.TTBestFinalKept

#assert_trust kernel NLA.Proofs.TR04.ttBest_relates
#print axioms NLA.Proofs.TR04.ttBest_relates

#assert_trust kernel NLA.Proofs.TR04.ttBestEntry_kept
#print axioms NLA.Proofs.TR04.ttBestEntry_kept

#assert_trust kernel NLA.Proofs.TR04.ttBest_halt_minimum_at
#print axioms NLA.Proofs.TR04.ttBest_halt_minimum_at

#assert_trust kernel NLA.Proofs.TR04.ttCandidate_store_disjoint
#print axioms NLA.Proofs.TR04.ttCandidate_store_disjoint

#assert_trust kernel NLA.Proofs.TR04.ttCandidate_copy_before_store
#print axioms NLA.Proofs.TR04.ttCandidate_copy_before_store

#assert_trust kernel NLA.Proofs.TR04.ttCandidate_copy_original_cells
#print axioms NLA.Proofs.TR04.ttCandidate_copy_original_cells

#assert_trust kernel NLA.Proofs.TR04.ttCandidate_copy_original_at
#print axioms NLA.Proofs.TR04.ttCandidate_copy_original_at

#assert_trust kernel NLA.Proofs.TR04.ttBestData_error_original
#print axioms NLA.Proofs.TR04.ttBestData_error_original

#assert_trust kernel NLA.Proofs.TR04.ttBest_halt_original_at
#print axioms NLA.Proofs.TR04.ttBest_halt_original_at
