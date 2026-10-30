import NLA.Proofs.TR04.MachineTTFinalContext
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
open NLA.Proofs.TR04 NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
open NLA.Proofs.TR04.TTMemoryLayout NLA.Proofs.TR04.TensorFormat NLA.Proofs.TR04.TensorFormat.TTStrict
namespace FinalContextExactConsumer
theorem literal_ttFirstContext_completed_minimum_at {start s0 : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (S : Shape) (r : Ranks S) (hr : ∀ j,1≤r j)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S)
    (hi : TTInitialSVDData S r A s0) {R : TTFirstReply s0} {hr0 : 1≤s0.natural 80}
    {n : ℕ} {ns : List ℕ} (hshape : modeList S.mode=s0.natural 81::n::ns)
    (hcols : suffixSize (n::ns)=s0.natural 82)
    (hctx : TTFirstContext R hr0 (ofShape S) (trace.state offset))
    (hl : (trace.state offset).label=189) (hs : (trace.state offset).status=.running)
    (hdone : (trace.state offset).natural 76=R.family.count)
    (hcompleted : TTCompletedCandidates S r A hshape R.family (trace.state offset) R.family.count) :
    ∃ extraTime : ℕ,∃ X : NLA.Computation.TensorTrainApproximation.Tensor S,
      extraTime=bestCandidateReturnTime (ttBestData (trace.state offset))+17 ∧
      Returns ttProgram S (trace.state (offset+extraTime)) X ∧
      Feasible S r X ∧
      (0<Optimum S r A → FrobeniusSq S A X<((S.order : ℝ)-1)*Optimum S r A) ∧
      (Optimum S r A=0 → X=A) ∧
      CostThrough ttProgram trace (offset+extraTime)≤CostThrough ttProgram trace offset+300*(Size S r+1)^2 := by
  exact ttFirstContext_completed_minimum_at ht offset S r hr A hi hshape hcols hctx hl hs hdone hcompleted
#assert_trust kernel literal_ttFirstContext_completed_minimum_at
#print axioms literal_ttFirstContext_completed_minimum_at
end FinalContextExactConsumer

#assert_trust kernel NLA.Proofs.TR04.ttFirstContext_completed_minimum_at
#print axioms NLA.Proofs.TR04.ttFirstContext_completed_minimum_at
