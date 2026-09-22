import NLA.IE21.FiniteTrimming
import NLA.IE21.SphereNet
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic

/-! Exact quadratic-form net control used for IE-21 covariance concentration.
Original analytic argument: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace
namespace NLA.IE21

lemma quadratic_lipschitz {n : ℕ} (B : Space n →L[ℝ] Space n)
    (x y : Space n) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    |inner ℝ (B x) x - inner ℝ (B y) y| ≤ 2 * ‖B‖ * ‖x - y‖ := by
  have heq : inner ℝ (B x) x - inner ℝ (B y) y =
      inner ℝ (B (x - y)) x + inner ℝ (B y) (x - y) := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  have h1 : |inner ℝ (B (x - y)) x| ≤ ‖B‖ * ‖x - y‖ := by
    calc
      _ ≤ ‖B (x - y)‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖B‖ * ‖x - y‖ := by simpa only [hx, mul_one] using B.le_opNorm (x - y)
  have h2 : |inner ℝ (B y) (x - y)| ≤ ‖B‖ * ‖x - y‖ := by
    calc
      _ ≤ ‖B y‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖B‖ * ‖x - y‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [hy, mul_one] using B.le_opNorm y
  rw [heq]
  have h := abs_add_le (inner ℝ (B (x - y)) x) (inner ℝ (B y) (x - y))
  linarith

lemma symmetric_norm_le_of_unit_quadratic {n : ℕ} (B : Space n →L[ℝ] Space n)
    (hB : B.IsSymmetric) (M : ℝ) (hM : 0 ≤ M)
    (hunit : ∀ x : Space n, ‖x‖ = 1 → |inner ℝ (B x) x| ≤ M) : ‖B‖ ≤ M := by
  rw [B.norm_eq_iSup_rayleighQuotient hB]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simpa [hx] using hM
  have hu : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := norm_smul_inv_norm hx
  have h := hunit (‖x‖⁻¹ • x) hu
  have hq : B.rayleighQuotient (‖x‖⁻¹ • x) = B.rayleighQuotient x :=
    B.rayleigh_smul x (inv_ne_zero (norm_ne_zero_iff.mpr hx))
  rw [← hq]
  simpa only [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real, hu, one_pow, div_one] using h

lemma symmetric_norm_le_net {n : ℕ} (B : Space n →L[ℝ] Space n)
    (hB : B.IsSymmetric) (C : Finset (Space n))
    (hC : ∀ y ∈ C, ‖y‖ = 1) (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : 2 * δ < 1)
    (hcover : ∀ x : Space n, ‖x‖ = 1 → ∃ y ∈ C, ‖x - y‖ ≤ δ)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ y ∈ C, |inner ℝ (B y) y| ≤ M) :
    ‖B‖ ≤ M / (1 - 2 * δ) := by
  have hglobal : ‖B‖ ≤ M + 2 * ‖B‖ * δ := by
    apply symmetric_norm_le_of_unit_quadratic B hB _ (by positivity)
    intro x hx
    obtain ⟨y, hyC, hxy⟩ := hcover x hx
    have hd := quadratic_lipschitz B x y hx (hC y hyC)
    have hd' : |inner ℝ (B x) x - inner ℝ (B y) y| ≤ 2 * ‖B‖ * δ :=
      hd.trans (mul_le_mul_of_nonneg_left hxy (by positivity))
    have ha := abs_add_le (inner ℝ (B x) x - inner ℝ (B y) y) (inner ℝ (B y) y)
    have hb := hbound y hyC
    simp only [sub_add_cancel] at ha
    linarith
  apply (le_div_iff₀ (by linarith : 0 < 1 - 2 * δ)).mpr
  nlinarith

def covarianceOperator {m n : ℕ} (A : Mat m n) : Space n →L[ℝ] Space n :=
  ((n : ℝ) / m) • ((matrixMap A).adjoint.comp (matrixMap A)) -
    ContinuousLinearMap.id ℝ (Space n)

lemma covarianceOperator_symmetric {m n : ℕ} (A : Mat m n) :
    (covarianceOperator A).IsSymmetric := by
  intro x y
  simp [covarianceOperator, inner_smul_left, inner_smul_right,
    inner_sub_left, inner_sub_right, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

lemma covariance_quadratic_norm {m n : ℕ} (A : Mat m n) (x : Space n) (hx : ‖x‖ = 1) :
    inner ℝ (covarianceOperator A x) x = (n : ℝ) / m * ‖matrixMap A x‖ ^ 2 - 1 := by
  simp [covarianceOperator, ContinuousLinearMap.comp_apply, inner_smul_left,
    inner_sub_left, ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K, hx]

lemma covariance_net_witness {m n : ℕ} (A : Mat m n) (C : Finset (Space n))
    (hC : ∀ y ∈ C, ‖y‖ = 1)
    (hcover : ∀ x : Space n, ‖x‖ = 1 → ∃ y ∈ C, ‖x - y‖ ≤ (1 : ℝ) / 4)
    (t : ℝ) (ht : 0 ≤ t) (hbad : t < covarianceError A) :
    ∃ y ∈ C, t / 2 < |inner ℝ (covarianceOperator A y) y| := by
  by_contra! h
  have hb := symmetric_norm_le_net (covarianceOperator A) (covarianceOperator_symmetric A)
    C hC (1 / 4) (by norm_num) (by norm_num) hcover (t / 2) (by positivity) h
  have heq : ‖covarianceOperator A‖ = covarianceError A := rfl
  rw [heq] at hb
  norm_num at hb
  linarith

lemma matrixMap_eq_inner_row {m n : ℕ} (A : Mat m n) (x : Space n) (i : Fin m) :
    matrixMap A x i = inner ℝ (matrixRow A i) x := by
  simp [matrixMap_apply, PiLp.inner_apply, matrixRow, RCLike.inner_apply, mul_comm]

lemma covariance_quadratic_rows {m n : ℕ} (A : Mat m n) (x : Space n) (hx : ‖x‖ = 1) :
    inner ℝ (covarianceOperator A x) x =
      (∑ i, directionalEnergy x (matrixRow A i)) / m - 1 := by
  rw [covariance_quadratic_norm A x hx, EuclideanSpace.real_norm_sq_eq]
  simp only [directionalEnergy, matrixMap_eq_inner_row, ← Finset.mul_sum]
  ring

end NLA.IE21
