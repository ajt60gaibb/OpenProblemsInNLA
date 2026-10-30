import NLA.Proofs.TR04.MachineTraceComposition

/-! Direct actual trace interfaces for scalar caller blocks and SVD opcodes.
All hypotheses describe finite literal code or actual memory/register values;
the trace always carries the model's own instruction charge. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

theorem trace_scalar_block_at {P : Program} {start : State P} {trace : Trace P}
    (ht : LegalTrace P start trace) (offset n : ℕ)
    (hscalar : ∀ k<n,((ordinaryStep P)^[k] (trace.state offset)).status=.running →
      instructionIsSVD (P.code ((ordinaryStep P)^[k] (trace.state offset)).label)=false) :
    trace.state (offset+n)=(ordinaryStep P)^[n] (trace.state offset) ∧
    CostThrough P trace (offset+n)≤CostThrough P trace offset+n := by
  have htail := legalTrace_shift ht offset
  have heq := legalTrace_scalar_prefix htail n hscalar
  have hc := costThrough_scalar_prefix htail n hscalar
  have hbound : CostThrough P (shiftedTrace trace offset) n≤n := by
    rw [hc]
    calc
      ∑ k ∈ Finset.range n,charge P ((ordinaryStep P)^[k] (trace.state offset))≤
          ∑ _k ∈ Finset.range n,1 := by
        apply Finset.sum_le_sum
        intro k hk
        exact charge_le_one_of_scalar (hscalar k (Finset.mem_range.mp hk))
      _=n := by simp
  exact ⟨heq,costThrough_compose_le le_rfl hbound⟩

/-- Every legal reply at a literal SVD opcode exposes its complete tuple and
actual cubic charge, including all rectangular and zero-dimensional cases. -/
theorem trace_svd_at {P : Program} {start : State P} {trace : Trace P}
    (ht : LegalTrace P start trace) (time : ℕ)
    (rows cols inputBase uBase sigmaBase vBase : Fin (P.extraNatRegisters+1))
    (next : Fin (P.extraLabels+1))
    (hcode : P.code (trace.state time).label=.svd rows cols inputBase uBase sigmaBase vBase next)
    (hs : (trace.state time).status=.running)
    (hd : OutputBlocksDisjoint ((trace.state time).natural rows) ((trace.state time).natural cols)
      ((trace.state time).natural uBase) ((trace.state time).natural sigmaBase) ((trace.state time).natural vBase)) :
    ∃ U : Matrix (Fin ((trace.state time).natural rows)) (Fin ((trace.state time).natural rows)) ℝ,
    ∃ sigma : Fin (min ((trace.state time).natural rows) ((trace.state time).natural cols)) → ℝ,
    ∃ V : Matrix (Fin ((trace.state time).natural cols)) (Fin ((trace.state time).natural cols)) ℝ,
      ValidSVD (readMatrix (trace.state time).memory ((trace.state time).natural rows)
        ((trace.state time).natural cols) ((trace.state time).natural inputBase)) U sigma V ∧
      trace.state (time+1) =
        { (trace.state time) with
          label := next
          memory := writeSVD (trace.state time).memory ((trace.state time).natural uBase)
            ((trace.state time).natural sigmaBase) ((trace.state time).natural vBase) U sigma V } ∧
      trace.cost time=(((trace.state time).natural rows)+((trace.state time).natural cols)+1)^3 := by
  have hstep := ht.2 time
  have hcost : trace.cost time=(((trace.state time).natural rows)+((trace.state time).natural cols)+1)^3 := by
    rw [step_cost_eq hstep]
    simp only [charge,hs,hcode]
  simp only [Step,hs,hcode,hd,if_pos] at hstep
  obtain ⟨_,U,sigma,V,hvalid,heq⟩ := hstep
  refine ⟨U,sigma,V,hvalid,?_,hcost⟩
  simpa only [hs] using heq

#assert_trust kernel trace_scalar_block_at
#assert_trust kernel trace_svd_at
#print axioms trace_scalar_block_at
#print axioms trace_svd_at
end NLA.Proofs.TR04
