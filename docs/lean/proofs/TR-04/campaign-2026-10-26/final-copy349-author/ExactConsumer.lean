import NLA.Proofs.TR04.MachineTTFinalCopy349
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
open NLA.Proofs.TR04 NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
namespace FinalCopy349ExactConsumer
theorem literal_ttCandidate_copy_setup349 (s : State ttProgram) (hl : s.label=349)
    (hs : s.status=.running) (hz : s.natural 127=0)
    (hptr : s.natural 123=ttCandidateStoreBase s) :
    (ordinaryStep ttProgram)^[6] s=ttCandidateCopyEntry s := by
  exact ttCandidate_copy_setup349 s hl hs hz hptr
#assert_trust kernel literal_ttCandidate_copy_setup349
#print axioms literal_ttCandidate_copy_setup349

theorem literal_ttCandidate_copy349_at {start : State ttProgram} {trace : Trace ttProgram}
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
  exact ttCandidate_copy349_at ht offset hl hs hz hptr hd
#assert_trust kernel literal_ttCandidate_copy349_at
#print axioms literal_ttCandidate_copy349_at

theorem literal_ttCandidate_copy349_original_at {start : State ttProgram} {trace : Trace ttProgram}
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
  exact ttCandidate_copy349_original_at ht offset S r B hl hs hz hptr hN hd hB
#assert_trust kernel literal_ttCandidate_copy349_original_at
#print axioms literal_ttCandidate_copy349_original_at

theorem literal349 : ttProgram.code 349 = .copyNat 21 127 350 := rfl
#assert_trust kernel literal349
#print axioms literal349

theorem literal354 : ttProgram.code 354 = .jump 33 := rfl
#assert_trust kernel literal354
#print axioms literal354

end FinalCopy349ExactConsumer

#assert_trust kernel NLA.Proofs.TR04.ttCandidate_copy_setup349
#print axioms NLA.Proofs.TR04.ttCandidate_copy_setup349

#assert_trust kernel NLA.Proofs.TR04.ttCandidate_copy349_at
#print axioms NLA.Proofs.TR04.ttCandidate_copy349_at

#assert_trust kernel NLA.Proofs.TR04.ttCandidate_copy349_original_at
#print axioms NLA.Proofs.TR04.ttCandidate_copy349_original_at
