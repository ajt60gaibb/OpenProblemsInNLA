import NLA.Proofs.TR04.MachineTTCompletedCandidates
import NLA.Proofs.TR04.MachineTTMinimumStrictRadix

/-! Final fixed-first-context wrapper. Dimension/rank transport is performed
on the entire tuple/family Pi property, before the actual reply is unpacked.
Only witnesses already tied to actual stored candidate slots are collected. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation TTMemoryLayout
open TensorFormat TensorFormat.TTStrict

/-- The actual completed candidate loop needs no additional mathematical
selection or Completion existence assumption at its final minimum phase. -/
theorem ttFirstContext_completed_minimum_at {start s0 : State ttProgram} {trace : Trace ttProgram}
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
  let s := trace.state offset
  let extraTime := bestCandidateReturnTime (ttBestData s)+17
  have hN : s.natural 64=DenseSize S := hctx.allocation.entries
  have hA : ∀ x,s.memory (s.natural 92+Offset S x)=A x := by
    intro x
    rw [hctx.allocation.input]
    have hoff := original_offset_lt_denseSize S x
    have hp : (ofShape S).input+Offset S x<(ofShape S).firstU := by
      change (ofShape S).input+Offset S x<(ofShape S).input+DenseSize S
      omega
    rw [hctx.savedPrefix _ hp,hi.memory]
    exact original_inputMemory_tensor_cell S r A x
  let Result : Prop :=
    ∃ X : NLA.Computation.TensorTrainApproximation.Tensor S,
      Returns ttProgram S (trace.state (offset+extraTime)) X ∧ Feasible S r X ∧
      (0<Optimum S r A → FrobeniusSq S A X<((S.order : ℝ)-1)*Optimum S r A) ∧
      (Optimum S r A=0 → X=A) ∧
      CostThrough ttProgram trace (offset+extraTime)≤CostThrough ttProgram trace offset+300*(Size S r+1)^2
  let P (cols rank : ℕ) (B : Matrix (Fin (s0.natural 81)) (Fin cols) ℝ) : Prop :=
    ∀ U : Matrix (Fin (s0.natural 81)) (Fin (s0.natural 81)) ℝ,
    ∀ sigma : Fin (min (s0.natural 81) cols) → ℝ,
    ∀ V : Matrix (Fin cols) (Fin cols) ℝ,
    ∀ hvalid : ValidSVD B U sigma V,
      let F := explicitFirstFrames hvalid rank
      s.natural 75=F.count → s.natural 76=F.count →
        TTCompletedCandidates S r A hshape F s F.count → Result
  have hcanonical : P (suffixSize (n::ns)) (originalRanks S r 0)
      (radixDenseFirst (Original.input hshape A)) := by
    intro U sigma V hvalid
    dsimp only
    let F := explicitFirstFrames hvalid (originalRanks S r 0)
    intro hcount hindex hcomplete
    obtain ⟨Z,hZ,hstored⟩ := TTCompletedCandidates.collect hcomplete
    have hfull : s.natural 75≤s.natural 76 := by omega
    obtain ⟨winner,hreturns,_,_,_,_,_,hfeas,hstrict,hzero,_,hcost⟩ :=
      ttBest_explicit_radix_strict_at S r hr A hshape hvalid Z hZ ht offset hl hs
        hctx.allocation.zero hcount hfull hN hA hstored
    exact ⟨Original.output hshape (completionOutput (F.frame winner) (Z winner)),
      hreturns,hfeas,hstrict,hzero,hcost⟩
  -- Transport the whole Pi property before touching fields of R. Both
  -- dimensions and the first-rank parameter now match the actual raw reply.
  have htransport (cols rank : ℕ) (hc : cols=suffixSize (n::ns)) (hrank : rank=originalRanks S r 0) :
      P cols rank (readMatrix s0.memory (s0.natural 81) cols (s0.natural 92)) := by
    subst cols
    subst rank
    rw [hi.read_original hshape]
    exact hcanonical
  have hactual := htransport (s0.natural 82) (s0.natural 80) hcols.symm hi.first_rank
  obtain ⟨X,hret,hfeas,hstrict,hzero,hcost⟩ :=
    hactual R.U R.sigma R.V R.valid hctx.count_eq hdone hcompleted
  exact ⟨extraTime,X,rfl,hret,hfeas,hstrict,hzero,hcost⟩

#assert_trust kernel ttFirstContext_completed_minimum_at
#print axioms ttFirstContext_completed_minimum_at
end NLA.Proofs.TR04
