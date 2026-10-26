import NLA.Proofs.TR04.MachineTraceComposition

/-! The literal arbitrary-SVD transition under finite register/label relocation.
No particular singular basis is selected; every legal caller reply is retained. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

/-- Extract every legal caller SVD response as an actual local response. -/
theorem RoutineEmbedding.svd_step {P Q : Program} (E : RoutineEmbedding P Q)
    {s : State P} {t t' : State Q} {cost : ℕ} (h : E.Relates s t)
    (hs : s.status = .running)
    (rows cols inputBase uBase sigmaBase vBase : Fin (P.extraNatRegisters + 1))
    (next : Fin (P.extraLabels + 1))
    (hi : P.code s.label = .svd rows cols inputBase uBase sigmaBase vBase next)
    (hd : OutputBlocksDisjoint (s.natural rows) (s.natural cols)
      (s.natural uBase) (s.natural sigmaBase) (s.natural vBase))
    (ht : Step Q t t' cost) :
    ∃ U : Matrix (Fin (s.natural rows)) (Fin (s.natural rows)) ℝ,
    ∃ sigma : Fin (min (s.natural rows) (s.natural cols)) → ℝ,
    ∃ V : Matrix (Fin (s.natural cols)) (Fin (s.natural cols)) ℝ,
      ValidSVD (readMatrix s.memory (s.natural rows) (s.natural cols) (s.natural inputBase)) U sigma V ∧
      E.Relates
        { s with
          label := next
          memory := writeSVD s.memory (s.natural uBase) (s.natural sigmaBase) (s.natural vBase) U sigma V } t' ∧
      cost = (s.natural rows + s.natural cols + 1)^3 := by
  classical
  have hexit : instructionIsHalt (P.code s.label) = false := by rw [hi];rfl
  have hcode : Q.code t.label =
      .svd (E.naturals rows) (E.naturals cols) (E.naturals inputBase)
        (E.naturals uBase) (E.naturals sigmaBase) (E.naturals vBase) (E.labels next) := by
    rw [h.label,E.code s.label hexit,hi]
    rfl
  have hcost : cost = (s.natural rows + s.natural cols + 1)^3 := by
    have hc := step_cost_eq ht
    rw [E.charge_eq h hexit] at hc
    simpa [charge,hs,hi] using hc
  have hreply := ht
  simp only [Step,h.status,hs,hcode] at hreply
  simp only [h.natural_apply rows,h.natural_apply cols,h.natural_apply inputBase,
    h.natural_apply uBase,h.natural_apply sigmaBase,h.natural_apply vBase,
    h.memory,hd,ite_true] at hreply
  rw [h.natural_apply rows,h.natural_apply cols] at hreply
  obtain ⟨_,U,sigma,V,hvalid,heq⟩ := hreply
  refine ⟨U,sigma,V,hvalid,?_,hcost⟩
  rw [heq]
  constructor
  · rfl
  · exact h.real
  · exact h.natural
  · rfl
  · exact hs.symm

/-- Each legal caller trace time at an SVD instruction exposes the full tuple
and its exact cubic charge, with no favorable-response assumption. -/
theorem RoutineEmbedding.svd_trace_step {P Q : Program} (E : RoutineEmbedding P Q)
    {s : State P} {start : State Q} {trace : Trace Q} (ht : LegalTrace Q start trace)
    (time : ℕ) (h : E.Relates s (trace.state time)) (hs : s.status = .running)
    (rows cols inputBase uBase sigmaBase vBase : Fin (P.extraNatRegisters + 1))
    (next : Fin (P.extraLabels + 1))
    (hi : P.code s.label = .svd rows cols inputBase uBase sigmaBase vBase next)
    (hd : OutputBlocksDisjoint (s.natural rows) (s.natural cols)
      (s.natural uBase) (s.natural sigmaBase) (s.natural vBase)) :
    ∃ U : Matrix (Fin (s.natural rows)) (Fin (s.natural rows)) ℝ,
    ∃ sigma : Fin (min (s.natural rows) (s.natural cols)) → ℝ,
    ∃ V : Matrix (Fin (s.natural cols)) (Fin (s.natural cols)) ℝ,
      ValidSVD (readMatrix s.memory (s.natural rows) (s.natural cols) (s.natural inputBase)) U sigma V ∧
      E.Relates
        { s with
          label := next
          memory := writeSVD s.memory (s.natural uBase) (s.natural sigmaBase) (s.natural vBase) U sigma V }
        (trace.state (time + 1)) ∧
      trace.cost time = (s.natural rows + s.natural cols + 1)^3 :=
  E.svd_step h hs rows cols inputBase uBase sigmaBase vBase next hi hd (ht.2 time)

#assert_trust kernel RoutineEmbedding.svd_step
#assert_trust kernel RoutineEmbedding.svd_trace_step
#print axioms RoutineEmbedding.svd_step
end NLA.Proofs.TR04
