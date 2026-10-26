import NLA.Proofs.TR04.MachineTTCandidateAll
import NLA.Proofs.TR04.MachineTTFinalContext
import NLA.Statements.TR04

/-! The unchanged original computational TR-04 boundary: one fixed finite
arithmetic/full-SVD program, every original input, every legal response trace,
actual dense output, fixed polynomial charge, feasibility and strict-or-zero. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation TTMemoryLayout

/-- The one fixed program succeeds on every legal full-SVD response trace.
The polynomial constants precede every original format, rank tuple and input. -/
theorem ttProgram_original_trace (S : Shape) (r : Ranks S) (hr : ∀ j,1≤r j)
    (A : Tensor S) (trace : Trace ttProgram)
    (ht : LegalTrace ttProgram (Start ttProgram S r A) trace) :
    ∃ t : ℕ,∃ X : Tensor S,
      Returns ttProgram S (trace.state t) X ∧
      CostThrough ttProgram trace t≤1000000*Size S r^5 ∧
      Feasible S r X ∧
      (0<Optimum S r A → FrobeniusSq S A X<((S.order : ℝ)-1)*Optimum S r A) ∧
      (Optimum S r A=0 → X=A) := by
  obtain ⟨offset,n,R,_,⟨hi,hphase⟩,_,ha,hj,_,_,_,_,_,_,hprefixCost⟩ :=
    ttInitial_explicit_family S r A hr trace ht
  let loopStart := offset+n
  have hc : TTFirstContext R (hi.rank_pos hr) (ofShape S) (trace.state loopStart) :=
    hphase.context hi ha
  obtain ⟨firstNext,ns,hshape,hcols,_⟩ := hi.two_format
  obtain ⟨elapsed,_,hlabel,hrunning,hfinal,hindex,hcompleted,hloopCost⟩ :=
    ttCandidates_all_at ht loopStart S r A hr hi hc hshape hcols hphase.1 hphase.2.1 hj
  obtain ⟨extraTime,X,_,hreturns,hfeasible,hstrict,hzero,hselectorCost⟩ :=
    ttFirstContext_completed_minimum_at ht (loopStart+elapsed) S r hr A hi hshape hcols
      hfinal hlabel hrunning hindex hcompleted
  have hsize := shape_denseSize_le_size S r
  have hpositive : 1≤Size S r := (shape_denseSize_pos S).trans_le hsize
  have hcount : R.family.count≤Size S r := by
    rw [←hc.count_eq]
    exact hc.count_le.trans hsize
  have hbudget := ttFullBudget_total (Size S r) R.family.count hpositive hcount
  refine ⟨loopStart+elapsed+extraTime,X,hreturns,?_,hfeasible,hstrict,hzero⟩
  change CostThrough ttProgram trace loopStart≤1024*(Size S r+1)^3 at hprefixCost
  omega

/-- Literal complete immutable original Target, with fixed P, C and k. -/
theorem fullTarget : NLA.Statements.TR04.Target := by
  refine ⟨ttProgram,1000000,5,by decide,?_⟩
  intro S r hr A
  refine ⟨ttProgram_trace_exists S r A,?_⟩
  intro trace ht
  exact ttProgram_original_trace S r hr A trace ht

#assert_trust kernel ttProgram_original_trace
#assert_trust kernel fullTarget
#print axioms ttProgram_original_trace
#print axioms fullTarget
end NLA.Proofs.TR04
