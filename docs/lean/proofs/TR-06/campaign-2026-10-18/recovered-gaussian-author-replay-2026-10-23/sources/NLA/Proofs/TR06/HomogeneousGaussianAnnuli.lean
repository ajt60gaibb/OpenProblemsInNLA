/-
Copyright (c) 2026. Released under Apache 2.0 license.
Actual dyadic annuli and integrals of homogeneous functions.
-/
import NLA.Proofs.TR06.HomogeneousGaussianScaling

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal NNReal Pointwise
open MeasureTheory Set
namespace NLA.Proofs.TR06.HomogeneousGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The actual punctured cone is covered by positive dyadic dilates of its
half-open reference annulus. No regularity or polar-coordinate premise is used. -/
theorem cone_eq_iUnion_annulus {C : Set E} (hC : PositiveCone C)
    (hzero : (0 : E) ∉ C) :
    C = ⋃ z : ℤ, (2 : ℝ) ^ z • annulus C := by
  ext x
  constructor
  · intro hx
    have hx0 : x ≠ 0 := by rintro rfl; exact hzero hx
    obtain ⟨z, hzle, hzlt⟩ := exists_mem_Ico_zpow (norm_pos_iff.mpr hx0)
      (by norm_num : (1 : ℝ) < 2)
    apply mem_iUnion.mpr
    refine ⟨z, ?_⟩
    have ht : 0 < (2 : ℝ) ^ z := zpow_pos (by norm_num) z
    refine ⟨((2 : ℝ) ^ z)⁻¹ • x, ?_, by simp [ht.ne']⟩
    refine ⟨(hC _ (inv_pos.mpr ht) x).mpr hx, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
      exact (le_inv_mul_iff₀ ht).mpr (by simpa using hzle)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
      apply (inv_mul_lt_iff₀ ht).mpr
      simpa [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), mul_comm] using hzlt
  · intro hx
    obtain ⟨z, y, hy, rfl⟩ := mem_iUnion.mp hx
    exact (hC _ (zpow_pos (by norm_num) z) y).mpr hy.1

/-- Actual Hausdorff annular integral scaling for homogeneous degree -p.
The dimension is q+p, so the resulting radial exponent is literally q. -/
theorem homogeneous_annular_integral (q p : ℕ) {C : Set E}
    (hC : MeasurableSet C) (f : E → ℝ≥0∞)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x ∈ C,
      f (t • x) = (ENNReal.ofReal (t ^ p))⁻¹ * f x)
    {t : ℝ} (ht : 0 < t) :
    (∫⁻ x in t • annulus C, f x ∂(μHE[q + p] : Measure E)) =
      ENNReal.ofReal (t ^ q) * ∫⁻ x in annulus C, f x ∂(μHE[q + p] : Measure E) := by
  rw [lintegral_scaled_set (q + p) ht]
  have heq : (∫⁻ x in annulus C, f (t • x) ∂(μHE[q+p] : Measure E)) =
      (ENNReal.ofReal (t ^ p))⁻¹ * ∫⁻ x in annulus C, f x ∂(μHE[q+p] : Measure E) := by
    rw [← lintegral_const_mul' _ _ (by finiteness : (ENNReal.ofReal (t ^ p))⁻¹ ≠ ⊤)]
    apply setLIntegral_congr_fun
    · exact hC.inter ((measurableSet_le measurable_const measurable_norm).inter
        (measurableSet_lt measurable_norm measurable_const))
    · intro x hx
      exact hhom t ht x hx.1
  rw [heq, pow_add, ENNReal.ofReal_mul (by positivity)]
  rw [mul_assoc (ENNReal.ofReal (t ^ q)),
    ← mul_assoc (ENNReal.ofReal (t ^ p)),
    ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul]

#print axioms cone_eq_iUnion_annulus
#print axioms homogeneous_annular_integral
#assert_trust kernel cone_eq_iUnion_annulus
#assert_trust kernel homogeneous_annular_integral
end NLA.Proofs.TR06.HomogeneousGaussian
