import NLA.Statements.TR04

/-! Elementary actual trace semantics for the unchanged exact arithmetic/SVD
machine. The SVD-totality premise is explicit supporting work, not a solver or
runtime oracle; the eventual target must discharge it by the full matrix proof. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

theorem step_cost_eq {P : Program} {s t : State P} {cost : ℕ}
    (h : Step P s t cost) : cost = charge P s := h.1

theorem step_of_halted {P : Program} {s t : State P} {cost base : ℕ}
    (hs : s.status = .halted base) :
    Step P s t cost ↔ cost = 0 ∧ t = s := by
  simp [Step, charge, hs]

theorem step_of_failed {P : Program} {s t : State P} {cost : ℕ}
    (hs : s.status = .failed) :
    Step P s t cost ↔ cost = 0 ∧ t = s := by
  simp [Step, charge, hs]

/-- A total concrete one-step relation supplies a legal infinite trace. Costs
are the machine's actual charges, never a freely supplied cost estimate. -/
theorem exists_legalTrace_of_step_total (P : Program)
    (htotal : ∀ s : State P, ∃ t : State P, Step P s t (charge P s))
    (start : State P) : ∃ trace : Trace P, LegalTrace P start trace := by
  classical
  let next : State P → State P := fun s => Classical.choose (htotal s)
  let states : ℕ → State P := Nat.rec start (fun _ s => next s)
  refine ⟨{ state := states, cost := fun k => charge P (states k) }, ?_⟩
  constructor
  · rfl
  · intro k
    change Step P (states k) (next (states k)) (charge P (states k))
    exact Classical.choose_spec (htotal (states k))

/-- Every scalar instruction has a successor. The only remaining totality
obligation of this exact model is a full SVD for each finite real matrix. -/
theorem step_total_of_svd_total
    (hsvd : ∀ (m l : ℕ) (B : Matrix (Fin m) (Fin l) ℝ),
      ∃ U sigma V, ValidSVD B U sigma V)
    (P : Program) (s : State P) :
    ∃ t : State P, Step P s t (charge P s) := by
  classical
  cases hs : s.status with
  | halted base =>
      exact ⟨s, (step_of_halted hs).2 ⟨by simp [charge, hs], rfl⟩⟩
  | failed =>
      exact ⟨s, (step_of_failed hs).2 ⟨by simp [charge, hs], rfl⟩⟩
  | running =>
      cases hi : P.code s.label <;>
        try (solve | refine ⟨ordinaryStep P s, ?_⟩; simp [Step, hs, hi])
      rename_i rows cols inputBase uBase sigmaBase vBase next
      by_cases hd : OutputBlocksDisjoint (s.natural rows) (s.natural cols)
          (s.natural uBase) (s.natural sigmaBase) (s.natural vBase)
      · obtain ⟨U, sigma, V, hvalid⟩ := hsvd (s.natural rows) (s.natural cols)
          (readMatrix s.memory (s.natural rows) (s.natural cols) (s.natural inputBase))
        refine ⟨{ s with
          label := next
          memory := writeSVD s.memory (s.natural uBase) (s.natural sigmaBase)
            (s.natural vBase) U sigma V }, ?_⟩
        simp only [Step, hs, hi, hd, ↓reduceIte, true_and]
        exact ⟨U, sigma, V, hvalid, rfl⟩
      · exact ⟨{ s with status := .failed }, by simp [Step, hs, hi, hd]⟩

theorem exists_legalTrace_of_svd_total
    (hsvd : ∀ (m l : ℕ) (B : Matrix (Fin m) (Fin l) ℝ),
      ∃ U sigma V, ValidSVD B U sigma V)
    (P : Program) (start : State P) :
    ∃ trace : Trace P, LegalTrace P start trace :=
  exists_legalTrace_of_step_total P (step_total_of_svd_total hsvd P) start

#assert_trust kernel step_cost_eq
#assert_trust kernel step_of_halted
#assert_trust kernel step_of_failed
#assert_trust kernel exists_legalTrace_of_step_total
#assert_trust kernel step_total_of_svd_total
#assert_trust kernel exists_legalTrace_of_svd_total
#print axioms exists_legalTrace_of_svd_total
end NLA.Proofs.TR04
