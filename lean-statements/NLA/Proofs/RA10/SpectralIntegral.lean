import NLA.Proofs.RA10.SpectralFunctionOperations
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Entrywise integration and nuclear bounds for the actual frozen spectral sums.
Trace duality avoids installing a second norm on matrices. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open MeasureTheory NLA.Statements.RA10

namespace NLA.Proofs.RA10

/-- A general integral bound for the exact sum-of-singular-values nuclear norm.
Only integrability of the finitely many entries and the scalar upper bound is needed. -/
theorem nuclearNorm_integral_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ} (M : Ω → Matrix (Fin n) (Fin n) ℝ) (g : Ω → ℝ)
    (hM : ∀ i j, Integrable (fun t => M t i j) μ) (hg : Integrable g μ)
    (hbound : ∀ t, NuclearNorm (M t) ≤ g t) :
    NuclearNorm (fun i j => ∫ t, M t i j ∂μ) ≤ ∫ t, g t ∂μ := by
  obtain ⟨U, hUtU, hUUt, hatt⟩ :=
    nuclearNorm_trace_orthogonal_attains (fun i j => ∫ t, M t i j ∂μ)
  have hrow (i : Fin n) : Integrable (fun t => ∑ j, U j i * M t j i) μ :=
    integrable_finsetSum _ fun j _ => (hM j i).const_mul (U j i)
  have hpair : Integrable (fun t => Matrix.trace (U.transpose * M t)) μ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    exact integrable_finsetSum _ fun i _ => hrow i
  have htrace : Matrix.trace (U.transpose *
      (show Matrix (Fin n) (Fin n) ℝ from fun i j => ∫ t, M t i j ∂μ)) =
      ∫ t, Matrix.trace (U.transpose * M t) ∂μ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    rw [integral_finsetSum _ (fun i _ => hrow i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => (hM j i).const_mul (U j i))]
    simp_rw [integral_const_mul]
    rfl
  rw [← hatt, htrace]
  exact integral_mono hpair hg fun t =>
    (nuclearNorm_trace_orthogonal_le U (M t) hUtU hUUt).trans (hbound t)

theorem functionMatrix_entry_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ} (g : Ω → ℝ → ℝ) (a : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ l, Integrable (fun t => g t (a l)) μ) (i j : Fin n) :
    Integrable (fun t => FunctionMatrix (g t) a Q i j) μ := by
  simp only [FunctionMatrix, SpectralMatrix, Matrix.of_apply]
  exact integrable_finsetSum _ fun l _ => ((hg l).mul_const (Q i l)).mul_const (Q j l)

theorem functionTruncation_entry_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ} (k : ℕ) (g : Ω → ℝ → ℝ) (a : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ l, Integrable (fun t => g t (a l)) μ) (i j : Fin n) :
    Integrable (fun t => FunctionTruncation k (g t) a Q i j) μ := by
  simp only [FunctionTruncation, Matrix.of_apply]
  apply integrable_finsetSum
  intro l _
  by_cases hl : l.val < k
  · simp only [if_pos hl]
    exact ((hg l).mul_const (Q i l)).mul_const (Q j l)
  · simp only [if_neg hl]
    exact integrable_zero _ _ _

theorem functionMatrix_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ} (g : Ω → ℝ → ℝ) (a : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ l, Integrable (fun t => g t (a l)) μ) :
    FunctionMatrix (fun x => ∫ t, g t x ∂μ) a Q =
      fun i j => ∫ t, FunctionMatrix (g t) a Q i j ∂μ := by
  ext i j
  simp only [FunctionMatrix, SpectralMatrix, Matrix.of_apply]
  rw [integral_finsetSum _ (fun l _ => ((hg l).mul_const (Q i l)).mul_const (Q j l))]
  simp_rw [integral_mul_const]

theorem functionTruncation_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ} (k : ℕ) (g : Ω → ℝ → ℝ) (a : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ l, Integrable (fun t => g t (a l)) μ) :
    FunctionTruncation k (fun x => ∫ t, g t x ∂μ) a Q =
      fun i j => ∫ t, FunctionTruncation k (g t) a Q i j ∂μ := by
  ext i j
  simp only [FunctionTruncation, Matrix.of_apply]
  have hint (l : Fin n) : Integrable
      (fun t => if l.val < k then g t (a l) * Q i l * Q j l else 0) μ := by
    by_cases hl : l.val < k
    · simp only [if_pos hl]
      exact ((hg l).mul_const (Q i l)).mul_const (Q j l)
    · simp only [if_neg hl]
      exact integrable_zero _ _ _
  rw [integral_finsetSum _ (fun l _ => hint l)]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : l.val < k <;> simp [hl, integral_mul_const]

#assert_trust kernel nuclearNorm_integral_le
#assert_trust kernel functionMatrix_entry_integrable
#assert_trust kernel functionTruncation_entry_integrable
#assert_trust kernel functionMatrix_integral
#assert_trust kernel functionTruncation_integral
#print axioms nuclearNorm_integral_le

end NLA.Proofs.RA10
