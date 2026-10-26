import NLA.Proofs.TR04.MachineTTStoreCandidate
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
open NLA.Proofs.TR04 NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
open NLA.Proofs.TR04.TTMemoryLayout NLA.Proofs.TR04.TensorFormat NLA.Proofs.TR04.TensorFormat.TTStrict
namespace StoreContextExactConsumer
theorem literal_ttStoresTensor_original_output (S : Shape) {ms : List ℕ}
    (hl : modeList S.mode=ms) (memory : ℕ → ℝ) (base : ℕ) (X : TensorFormat.Tensor ms)
    (hX : StoresTensor memory base ms X) :
    ∀ x,memory (base+Offset S x)=Original.output hl X x := by
  exact ttStoresTensor_original_output S hl memory base X hX
#assert_trust kernel literal_ttStoresTensor_original_output
#print axioms literal_ttStoresTensor_original_output

theorem literal_ttCandidate_store_context_at {start s0 : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (S : Shape) (r : Ranks S) (A : NLA.Computation.TensorTrainApproximation.Tensor S)
    (hi : TTInitialSVDData S r A s0) {R : TTFirstReply s0} {hr : 1≤s0.natural 80}
    (L : Layout) (hctx : TTFirstContext R hr L (trace.state offset))
    {ms : List ℕ} (hshape : modeList S.mode=ms) (X : TensorFormat.Tensor ms)
    (hl : (trace.state offset).label=349) (hs : (trace.state offset).status=.running)
    (hpair : TTWorkPair L (trace.state offset))
    (hptr : (trace.state offset).natural 123=ttCandidateStoreBase (trace.state offset))
    (hX : StoresTensor (trace.state offset).memory ((trace.state offset).natural 89) ms X) :
    let s := trace.state offset
    let elapsed := 6*DenseSize S+10
    let time := offset+elapsed
    elapsed≤18*(Size S r+1) ∧
      (trace.state time).label=189 ∧ (trace.state time).status=.running ∧
      TTFirstContext R hr L (trace.state time) ∧
      (trace.state time).natural 76=s.natural 76+1 ∧
      (∀ x,(trace.state time).memory (L.candidate (s.natural 76)+Offset S x)=Original.output hshape X x) ∧
      (∀ i<s.natural 76,∀ k<DenseSize S,
        (trace.state time).memory (L.candidate i+k)=s.memory (L.candidate i+k)) ∧
      (∀ a,a<L.childSigma → (trace.state time).memory a=s.memory a) ∧
      TTWorkPair L (trace.state time) ∧
      (∀ j : Fin 128,TTCopyFinalKept j → (trace.state time).natural j=s.natural j) ∧
      CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+18*(Size S r+1) := by
  exact ttCandidate_store_context_at ht offset S r A hi L hctx hshape X hl hs hpair hptr hX
#assert_trust kernel literal_ttCandidate_store_context_at
#print axioms literal_ttCandidate_store_context_at

end StoreContextExactConsumer

#assert_trust kernel NLA.Proofs.TR04.ttStoresTensor_original_output
#print axioms NLA.Proofs.TR04.ttStoresTensor_original_output

#assert_trust kernel NLA.Proofs.TR04.ttLoopKept_copyFinal
#print axioms NLA.Proofs.TR04.ttLoopKept_copyFinal

#assert_trust kernel NLA.Proofs.TR04.tt_childSigma_le_store
#print axioms NLA.Proofs.TR04.tt_childSigma_le_store

#assert_trust kernel NLA.Proofs.TR04.ttCandidate_store_context_at
#print axioms NLA.Proofs.TR04.ttCandidate_store_context_at
