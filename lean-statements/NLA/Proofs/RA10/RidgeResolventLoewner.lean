import NLA.Proofs.RA10.MatchedLeadingRidge
import NLA.Proofs.RA10.SpectralQuadratic
import NLA.Proofs.RA10.SelectedProjectionFunction
import Mathlib.Tactic.FieldSimp

/-! RA-10 sharp Loewner bounds for ridge resolvents. These are exact
factor bounds underlying source Equation (14); the operator-norm conversion,
nuclear ideal inequality, and full target remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

private theorem spectralMatrix_positiveSemidefinite {n : ℕ}
    (w : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hw : ∀ a, 0 ≤ w a) :
    NLA.Statements.RA10.PositiveSemidefinite
      (NLA.Statements.RA10.SpectralMatrix w Q) := by
  constructor
  · intro i j
    simp only [NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro a _
    ring
  · intro x
    rw [spectralMatrix_quadratic_form]
    apply Finset.sum_nonneg
    intro a _
    exact mul_nonneg (hw a) (sq_nonneg _)

theorem spectralShift_resolvent_nonnegative {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q) :
    NLA.Statements.RA10.PositiveSemidefinite
      ((s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹) := by
  rw [← spectralShift_inverse hs h]
  change NLA.Statements.RA10.PositiveSemidefinite
    (NLA.Statements.RA10.SpectralMatrix (fun a => 1 / (s + eigenvalues a)) Q)
  apply spectralMatrix_positiveSemidefinite
  intro a
  have hpos : 0 < s + eigenvalues a := by linarith [h.1 a]
  exact le_of_lt (one_div_pos.mpr hpos)

theorem spectralShift_resolvent_upperBound {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q) :
    NLA.Statements.RA10.PositiveSemidefinite
      ((1 / s) • (1 : Matrix (Fin n) (Fin n) ℝ) -
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹) := by
  have hQTQ : Q.transpose * Q = 1 := by
    ext a b
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h.2.2.1 a b
  have hQQT : Q * Q.transpose = 1 := mul_eq_one_comm.mp hQTQ
  have hrow (i j : Fin n) :
      (∑ a : Fin n, Q i a * Q j a) = if i = j then 1 else 0 := by
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hQQT
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hij
  have hrep :
      (1 / s) • (1 : Matrix (Fin n) (Fin n) ℝ) -
          (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹ =
        NLA.Statements.RA10.SpectralMatrix
          (fun a => 1 / s - 1 / (s + eigenvalues a)) Q := by
    rw [← spectralShift_inverse hs h]
    ext i j
    simp only [NLA.Statements.RA10.FunctionMatrix,
      NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    calc
      (1 / s) * (if i = j then (1 : ℝ) else 0) -
          ∑ a : Fin n, 1 / (s + eigenvalues a) * Q i a * Q j a =
          (1 / s) * (∑ a : Fin n, Q i a * Q j a) -
            ∑ a : Fin n, 1 / (s + eigenvalues a) * Q i a * Q j a := by rw [hrow]
      _ = ∑ a : Fin n, (1 / s - 1 / (s + eigenvalues a)) * Q i a * Q j a := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro a _
        ring
  rw [hrep]
  apply spectralMatrix_positiveSemidefinite
  intro a
  have hpos : 0 < s + eigenvalues a := by linarith [h.1 a]
  have heq : 1 / s - 1 / (s + eigenvalues a) =
      eigenvalues a / (s * (s + eigenvalues a)) := by
    field_simp [ne_of_gt hs, ne_of_gt hpos]
    ring
  rw [heq]
  exact div_nonneg (h.1 a) (le_of_lt (mul_pos hs hpos))

theorem selectedCutoffIndex_exists {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n) :
    ∃ j : Fin n, j.val + 1 = k := by
  refine ⟨⟨k - 1, ?_⟩, ?_⟩
  · omega
  · change k - 1 + 1 = k
    omega

#assert_trust kernel spectralShift_resolvent_nonnegative
#assert_trust kernel spectralShift_resolvent_upperBound
#assert_trust kernel selectedCutoffIndex_exists
#print axioms spectralShift_resolvent_upperBound

end NLA.Proofs.RA10
