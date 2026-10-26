import NLA.Proofs.IE22.ExtremaBounds
import NLA.Proofs.IE22.GaussianTrimming

/-! Transport from actual squared geometric endpoints to the literal
eventual-uniform comparison. The full proof supplies both endpoints separately. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.IE22
open NLA.Statements.RowDeletion NLA.Statements.IE22

theorem uniformUpper_of_squared_bound {θ a : ℝ} (hθ : θ ≤ 1) (ha : 0 ≤ a)
    (hupper : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n m : ℕ, 0 < n → 0 < m → N ≤ n →
        ∀ A : Matrix (Fin m) (Fin n) ℝ, UnitRows A →
          (n : ℝ) / (m : ℝ) * SubsingularSquared θ A ≤ TrimmedMoment a + ε) :
    UniformUpper θ (Real.sqrt (TrimmedMoment a)) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hupper (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, 0, ?_⟩
  intro n m hn _hm hnN _hR
  apply extremum_le_of_squared_bound hθ hn
    (add_nonneg (Real.sqrt_nonneg _) hε.le)
  intro A hA
  have h := hN n m hn _hm hnN A hA
  have hs := Real.sq_sqrt (trimmedMoment_nonneg ha)
  have hp := Real.sqrt_nonneg (TrimmedMoment a)
  nlinarith

theorem not_uniformUpper_of_squared_witness {θ a : ℝ} (hθ : θ ≤ 1) (ha : 0 ≤ a)
    (hwitness : ∀ ε : ℝ, 0 < ε → ∀ N R : ℕ,
      ∃ n m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℝ,
        0 < n ∧ 0 < m ∧ N ≤ n ∧ R * n ≤ m ∧ UnitRows A ∧
          TrimmedMoment a - ε ≤ (n : ℝ) / (m : ℝ) * SubsingularSquared θ A) :
    ∀ c' : ℝ, c' < Real.sqrt (TrimmedMoment a) → ¬ UniformUpper θ c' := by
  intro c' hc' hbad
  by_cases hc0 : c' < 0
  · have hε : 0 < -c' / 2 := by linarith
    obtain ⟨N, R, hNR⟩ := hbad (-c' / 2) hε
    obtain ⟨n, m, A, hn, hm, hnN, hRm, _hA, _henergy⟩ :=
      hwitness 1 (by norm_num) N R
    have hu := hNR n m hn hm hnN hRm
    have hl := extremum_nonneg hθ hn hm
    linarith
  · have hc0' : 0 ≤ c' := le_of_not_gt hc0
    let b : ℝ := (c' + Real.sqrt (TrimmedMoment a)) / 2
    let ε : ℝ := (Real.sqrt (TrimmedMoment a) - c') / 4
    have hroot : 0 ≤ Real.sqrt (TrimmedMoment a) := Real.sqrt_nonneg _
    have hb : 0 ≤ b := by dsimp [b]; positivity
    have hbroot : b < Real.sqrt (TrimmedMoment a) := by dsimp [b]; linarith
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hgap : 0 < TrimmedMoment a - b ^ 2 := by
      have hsq := (sq_lt_sq₀ hb hroot).2 hbroot
      rw [Real.sq_sqrt (trimmedMoment_nonneg ha)] at hsq
      linarith
    obtain ⟨N, R, hNR⟩ := hbad ε hε
    obtain ⟨n, m, A, hn, hm, hnN, hRm, hA, henergy⟩ :=
      hwitness (TrimmedMoment a - b ^ 2) hgap N R
    have hbenergy : b ^ 2 ≤ (n : ℝ) / (m : ℝ) * SubsingularSquared θ A := by
      linarith
    have hbvalue : b ≤ normalizedSubsingular θ A := by
      apply (sq_le_sq₀ hb (normalizedSubsingular_nonneg θ A)).1
      rw [normalizedSubsingular_sq hθ hn]
      exact hbenergy
    have hl := normalizedSubsingular_le_extremum hθ hn hm A hA
    have hu := hNR n m hn hm hnN hRm
    dsimp [b, ε] at hbvalue hu
    linarith

#assert_trust kernel uniformUpper_of_squared_bound
#assert_trust kernel not_uniformUpper_of_squared_witness
#print axioms uniformUpper_of_squared_bound
#print axioms not_uniformUpper_of_squared_witness
end NLA.Proofs.IE22
