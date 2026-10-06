/-
Released under Apache 2.0; see LICENSE.
AI-assisted Gaussian quadratic core, proved directly from the pinned Mathlib.
Exact statements and preimplementation review are recorded in
reviews/gaussian-quadratic-specification.md. No manuscript theorem is assumed.
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace NLA.IE06.GaussianQuadratic

def gaussianVector (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => gaussianReal 0 1

instance gaussianVector_probability (d : ℕ) : IsProbabilityMeasure (gaussianVector d) := by
  unfold gaussianVector
  infer_instance

def weightedSquares {d : ℕ} (w : Fin d → ℝ) (z : Fin d → ℝ) : ℝ :=
  ∑ i, w i * (z i) ^ 2

private theorem weighted_pdf (s z : ℝ) :
    gaussianPDFReal 0 1 z * Real.exp (s * z ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1 : ℝ) / 2 - s) * z ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The exact scalar quadratic moment integral, including negative parameters. -/
theorem scalar_quadratic_mgf (s : ℝ) (hs : s < 1 / 2) :
    Integrable (fun z : ℝ => Real.exp (s * z ^ 2)) (gaussianReal 0 1) ∧
      (∫ z : ℝ, Real.exp (s * z ^ 2) ∂gaussianReal 0 1) =
        (Real.sqrt (1 - 2 * s))⁻¹ := by
  have hb : 0 < (1 : ℝ) / 2 - s := by linarith
  have hd : 0 < 1 - 2 * s := by linarith
  have hi : Integrable (fun z : ℝ => gaussianPDFReal 0 1 z * Real.exp (s * z ^ 2)) := by
    simp_rw [weighted_pdf]
    exact (integrable_exp_neg_mul_sq hb).const_mul _
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  constructor
  · apply (integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF 0 1) (ae_of_all _ fun _ => gaussianPDF_lt_top)).mpr
    simpa only [toReal_gaussianPDF, smul_eq_mul] using hi
  · erw [integral_withDensity_eq_integral_toReal_smul
      (measurable_gaussianPDF 0 1) (ae_of_all _ fun _ => gaussianPDF_lt_top)]
    simp only [toReal_gaussianPDF, smul_eq_mul]
    simp_rw [weighted_pdf]
    rw [integral_const_mul, integral_gaussian]
    have hratio : Real.pi / ((1 : ℝ) / 2 - s) = (2 * Real.pi) / (1 - 2 * s) := by
      field_simp
    rw [hratio, Real.sqrt_div (by positivity) (1 - 2 * s)]
    have hc : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp

private theorem exponential_sum_product {d : ℕ} (w z : Fin d → ℝ) (t : ℝ) :
    Real.exp (t * weightedSquares w z) = ∏ i, Real.exp ((t * w i) * (z i) ^ 2) := by
  rw [weightedSquares, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  ring

/-- Exact finite independent-Gaussian quadratic MGF and its integrability. -/
theorem weighted_quadratic_mgf {d : ℕ} (w : Fin d → ℝ) (t : ℝ)
    (ht : ∀ i, t * w i < 1 / 2) :
    Integrable (fun z => Real.exp (t * weightedSquares w z)) (gaussianVector d) ∧
      (∫ z, Real.exp (t * weightedSquares w z) ∂gaussianVector d) =
        ∏ i, (Real.sqrt (1 - 2 * (t * w i)))⁻¹ := by
  simp_rw [exponential_sum_product]
  constructor
  · exact Integrable.fintype_prod (fun i => (scalar_quadratic_mgf (t * w i) (ht i)).1)
  · rw [gaussianVector, integral_fintype_prod_eq_prod (fun i z => Real.exp ((t * w i) * z ^ 2))]
    exact Finset.prod_congr rfl (fun i _ => (scalar_quadratic_mgf (t * w i) (ht i)).2)

/-- Exact small-parameter estimate, with a closed upper endpoint. -/
theorem scalar_mgf_bound (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1 / 4) :
    (Real.sqrt (1 - 2 * s))⁻¹ ≤ Real.exp (2 * s) := by
  have hd : 0 < 1 - 2 * s := by linarith
  have hinv : (1 - 2 * s)⁻¹ ≤ 1 + 4 * s := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hd).mpr
    have hh : 0 ≤ s * (1 - 4 * s) := mul_nonneg hs (by linarith)
    nlinarith
  have hlog := Real.one_sub_inv_le_log_of_pos hd
  have hpos : 0 < (Real.sqrt (1 - 2 * s))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr hd)
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  rw [Real.log_inv, Real.log_sqrt hd.le]
  linarith

/-- MGF estimate at the exact Chernoff parameter, retaining explicit integrability. -/
theorem weighted_mgf_bound {d : ℕ} (w : Fin d → ℝ) (L : ℝ) (hL : 0 < L)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ L) :
    Integrable (fun z => Real.exp ((1 / (4 * L)) * weightedSquares w z))
      (gaussianVector d) ∧
    (∫ z, Real.exp ((1 / (4 * L)) * weightedSquares w z) ∂gaussianVector d) ≤
      Real.exp ((∑ i, w i) / (2 * L)) := by
  have ht : 0 < (1 : ℝ) / (4 * L) := by positivity
  have hcoord (i : Fin d) : 0 ≤ (1 / (4 * L)) * w i ∧ (1 / (4 * L)) * w i ≤ 1 / 4 := by
    refine ⟨mul_nonneg ht.le (hw i).1, ?_⟩
    calc
      (1 / (4 * L)) * w i ≤ (1 / (4 * L)) * L :=
        mul_le_mul_of_nonneg_left (hw i).2 ht.le
      _ = 1 / 4 := by field_simp
  have hstrict (i : Fin d) : (1 / (4 * L)) * w i < 1 / 2 := by
    linarith [(hcoord i).2]
  obtain ⟨hi, heq⟩ := weighted_quadratic_mgf w (1 / (4 * L)) hstrict
  refine ⟨hi, ?_⟩
  rw [heq]
  calc
    ∏ i, (Real.sqrt (1 - 2 * ((1 / (4 * L)) * w i)))⁻¹ ≤
        ∏ i, Real.exp (2 * ((1 / (4 * L)) * w i)) := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        exact scalar_mgf_bound _ (hcoord i).1 (hcoord i).2
    _ = Real.exp ((∑ i, w i) / (2 * L)) := by
      rw [← Real.exp_sum]
      congr 1
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring

/-- Independent Gaussian weighted-square concentration with exact constants.
The matrix/Frobenius bridge is not assumed or asserted by this theorem. -/
theorem weighted_square_tail {d : ℕ} (w : Fin d → ℝ) (L x : ℝ)
    (hL : 0 < L) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ L) (_hx : 0 < x) :
    gaussianVector d {z | 2 * (∑ i, w i) + 4 * L * x < weightedSquares w z} ≤
      ENNReal.ofReal (Real.exp (-x)) := by
  obtain ⟨hi, hmgf⟩ := weighted_mgf_bound w L hL hw
  have ht : 0 ≤ (1 : ℝ) / (4 * L) := by positivity
  have hchernoff := measure_ge_le_exp_mul_mgf
    (μ := gaussianVector d) (X := weightedSquares w)
    (2 * (∑ i, w i) + 4 * L * x) ht hi
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr
  change (gaussianVector d).real _ ≤ _
  calc
    (gaussianVector d).real {z | 2 * (∑ i, w i) + 4 * L * x < weightedSquares w z} ≤
        (gaussianVector d).real {z | 2 * (∑ i, w i) + 4 * L * x ≤ weightedSquares w z} :=
      measureReal_mono (by
        intro z hz
        change 2 * (∑ i, w i) + 4 * L * x ≤ weightedSquares w z
        exact le_of_lt hz)
    _ ≤ Real.exp (-(1 / (4 * L)) * (2 * (∑ i, w i) + 4 * L * x)) *
        (∫ z, Real.exp ((1 / (4 * L)) * weightedSquares w z) ∂gaussianVector d) := hchernoff
    _ ≤ Real.exp (-(1 / (4 * L)) * (2 * (∑ i, w i) + 4 * L * x)) *
        Real.exp ((∑ i, w i) / (2 * L)) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-x) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring

#assert_trust kernel scalar_quadratic_mgf
#assert_trust kernel weighted_quadratic_mgf
#assert_trust kernel scalar_mgf_bound
#assert_trust kernel weighted_mgf_bound
#assert_trust kernel weighted_square_tail
#print axioms scalar_quadratic_mgf
#print axioms weighted_quadratic_mgf
#print axioms scalar_mgf_bound
#print axioms weighted_mgf_bound
#print axioms weighted_square_tail

end NLA.IE06.GaussianQuadratic
