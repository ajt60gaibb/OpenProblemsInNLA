import NLA.Proofs.PF05.Basic

/-! Coordinate consequences for a nonzero orthogonal PSD pair in size two.
This module does not yet construct the normalizing congruence. -/
set_option autoImplicit false
namespace NLA.Proofs.PF05
open NLA.Statements.PF05

theorem nonzero_psd_two_positive_diagonal
    (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : PositiveSemidefinite A) (hne : A ≠ 0) :
    0 < A 0 0 ∨ 0 < A 1 1 := by
  have h00 := psd_diag_nonneg A hA 0
  have h11 := psd_diag_nonneg A hA 1
  by_contra! h
  have hz00 : A 0 0 = 0 := le_antisymm h.1 h00
  have hz11 : A 1 1 = 0 := le_antisymm h.2 h11
  obtain ⟨h01, h10⟩ := psd_zero_00_offdiag A hA hz00
  apply hne
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hz00, hz11, h01, h10]

theorem zero_pair_coordinates_of_A00_pos
    (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : PositiveSemidefinite A) (hB : PositiveSemidefinite B)
    (hB0 : B ≠ 0) (htrace : Matrix.trace (A * B) = 0)
    (ha : 0 < A 0 0) :
    0 < B 1 1 ∧
    A 0 0 * A 1 1 = (A 0 1)^2 ∧
    A 0 0 * B 0 1 + A 0 1 * B 1 1 = 0 ∧
    A 0 0 * B 0 0 + A 0 1 * B 0 1 = 0 := by
  have hAB := psd_trace_zero_mul_eq_zero A B hA hB htrace
  have hdetA : A.det = 0 := det_zero_of_mul_zero_right_nonzero A B hAB hB0
  have hAeq : A 0 0 * A 1 1 = (A 0 1)^2 := by
    rw [Matrix.det_fin_two, hA.1 1 0] at hdetA
    nlinarith
  have hprod00 : A 0 0 * B 0 0 + A 0 1 * B 1 0 = 0 := by
    have hh := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℝ => X 0 0) hAB
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using hh
  have hprod01 : A 0 0 * B 0 1 + A 0 1 * B 1 1 = 0 := by
    have hh := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℝ => X 0 1) hAB
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using hh
  have hB11 : 0 < B 1 1 := by
    have hnonneg := psd_diag_nonneg B hB 1
    by_contra! hn
    have hz11 : B 1 1 = 0 := le_antisymm hn hnonneg
    obtain ⟨hz01, hz10⟩ := psd_zero_11_offdiag B hB hz11
    have hz00 : B 0 0 = 0 := by
      rw [hz10] at hprod00
      nlinarith
    apply hB0
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hz00, hz11, hz01, hz10]
  refine ⟨hB11, hAeq, hprod01, ?_⟩
  rwa [hB.1 1 0] at hprod00

theorem zero_pair_coordinates_of_A11_pos
    (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : PositiveSemidefinite A) (hB : PositiveSemidefinite B)
    (hB0 : B ≠ 0) (htrace : Matrix.trace (A * B) = 0)
    (hc : 0 < A 1 1) :
    0 < B 0 0 ∧
    A 0 0 * A 1 1 = (A 0 1)^2 ∧
    A 0 1 * B 0 0 + A 1 1 * B 0 1 = 0 ∧
    A 0 1 * B 0 1 + A 1 1 * B 1 1 = 0 := by
  have hAB := psd_trace_zero_mul_eq_zero A B hA hB htrace
  have hdetA : A.det = 0 := det_zero_of_mul_zero_right_nonzero A B hAB hB0
  have hAeq : A 0 0 * A 1 1 = (A 0 1)^2 := by
    rw [Matrix.det_fin_two, hA.1 1 0] at hdetA
    nlinarith
  have hprod10 : A 1 0 * B 0 0 + A 1 1 * B 1 0 = 0 := by
    have hh := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℝ => X 1 0) hAB
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using hh
  have hprod11 : A 1 0 * B 0 1 + A 1 1 * B 1 1 = 0 := by
    have hh := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℝ => X 1 1) hAB
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using hh
  have hB00 : 0 < B 0 0 := by
    have hnonneg := psd_diag_nonneg B hB 0
    by_contra! hn
    have hz00 : B 0 0 = 0 := le_antisymm hn hnonneg
    obtain ⟨hz01, hz10⟩ := psd_zero_00_offdiag B hB hz00
    have hz11 : B 1 1 = 0 := by
      rw [hz01] at hprod11
      rw [hA.1 1 0] at hprod11
      nlinarith
    apply hB0
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hz00, hz11, hz01, hz10]
  refine ⟨hB00, hAeq, ?_, ?_⟩
  · rwa [hA.1 1 0, hB.1 1 0] at hprod10
  · rwa [hA.1 1 0] at hprod11

end NLA.Proofs.PF05
