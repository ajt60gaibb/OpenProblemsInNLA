/-
Copyright (c) 2026. Released under Apache 2.0 license.
Hausdorff-cone Gaussian integrability from actual annular integrals.
-/
import NLA.Proofs.TR06.HomogeneousGaussianAnnuli
import NLA.Proofs.TR06.HomogeneousGaussianSeries

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal NNReal Pointwise
open MeasureTheory Set

namespace NLA.Proofs.TR06.HomogeneousGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The actual Gaussian weight used by the tensor model. -/
def gaussian (x : E) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (- ‖x‖ ^ 2 / 2))

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem gaussian_pos (x : E) : 0 < gaussian x := ENNReal.ofReal_pos.mpr (Real.exp_pos _)

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem gaussian_le_one (x : E) : gaussian x ≤ 1 := by
  exact (ENNReal.ofReal_le_one).mpr (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x‖]))

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem gaussian_le_of_norm {t : ℝ} (ht : 0 ≤ t) {x : E} (hx : t ≤ ‖x‖) :
    gaussian x ≤ ENNReal.ofReal (Real.exp (- t ^ 2 / 2)) := by
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  nlinarith [norm_nonneg x]

omit [MeasurableSpace E] [BorelSpace E] in
theorem norm_lower_of_mem_scaled_annulus {C : Set E} {t : ℝ} (ht : 0 < t)
    {x : E} (hx : x ∈ t • annulus C) : t ≤ ‖x‖ := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  nlinarith [hy.2.1]

omit [NormedSpace ℝ E] in
theorem measurableSet_annulus {C : Set E} (hC : MeasurableSet C) :
    MeasurableSet (annulus C) :=
  hC.inter ((measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const))

/-- Gaussian-weighted integral on one actual dilated annulus. -/
theorem gaussian_scaled_annular_bound (q p : ℕ) {C : Set E} (hC : MeasurableSet C)
    (f : E → ℝ≥0∞)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x ∈ C,
      f (t • x) = (ENNReal.ofReal (t ^ p))⁻¹ * f x)
    {t : ℝ} (ht : 0 < t) :
    (∫⁻ x in t • annulus C, f x * gaussian x ∂(μHE[q+p] : Measure E)) ≤
      ENNReal.ofReal (t ^ q * Real.exp (- t ^ 2 / 2)) *
        ∫⁻ x in annulus C, f x ∂(μHE[q+p] : Measure E) := by
  calc
    _ ≤ ∫⁻ x in t • annulus C,
        ENNReal.ofReal (Real.exp (-t^2/2)) * f x ∂(μHE[q+p] : Measure E) := by
      apply setLIntegral_mono' ((measurableSet_annulus hC).const_smul₀ t)
      intro x hx
      rw [mul_comm _ (f x)]
      gcongr
      exact gaussian_le_of_norm ht.le (norm_lower_of_mem_scaled_annulus ht hx)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        homogeneous_annular_integral q p hC f hhom ht, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity)]
      rw [mul_comm (Real.exp (-t^2/2)) (t^q)]

/-- Full Gaussian integrability follows from the literal annular integral of a
homogeneous function. The radial exponent q is positive; no polar formula or
semialgebraic-volume theorem is assumed. -/
theorem gaussian_lintegral_lt_top (q p : ℕ) (hq : 0 < q)
    {C : Set E} (hC : MeasurableSet C) (hcone : PositiveCone C)
    (hzero : (0 : E) ∉ C) (f : E → ℝ≥0∞)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x ∈ C,
      f (t • x) = (ENNReal.ofReal (t ^ p))⁻¹ * f x)
    (hfinite : (∫⁻ x in annulus C, f x ∂(μHE[q+p] : Measure E)) < ⊤) :
    (∫⁻ x in C, f x * gaussian x ∂(μHE[q+p] : Measure E)) < ⊤ := by
  let I : ℝ≥0∞ := ∫⁻ x in annulus C, f x ∂(μHE[q+p] : Measure E)
  have hb (z : ℤ) :
      (∫⁻ x in (2 : ℝ)^z • annulus C, f x * gaussian x ∂(μHE[q+p] : Measure E)) ≤
      ENNReal.ofReal (dyadicCoefficient q z) * I := by
    cases z with
    | ofNat n =>
      simpa [dyadicCoefficient, Int.ofNat_eq_natCast, I] using
        gaussian_scaled_annular_bound q p hC f hhom (pow_pos (by norm_num) n)
    | negSucc n =>
      have ht : 0 < (2 : ℝ) ^ (Int.negSucc n) := zpow_pos (by norm_num) _
      calc
        _ ≤ ∫⁻ x in (2 : ℝ)^(Int.negSucc n) • annulus C,
            f x ∂(μHE[q+p] : Measure E) := by
          apply lintegral_mono
          intro x
          calc
            f x * gaussian x ≤ f x * 1 := by gcongr; exact gaussian_le_one x
            _ = f x := mul_one _
        _ = ENNReal.ofReal (((2 : ℝ)^(Int.negSucc n))^q) * I :=
          homogeneous_annular_integral q p hC f hhom ht
        _ = _ := by
          congr 2
          simp only [dyadicCoefficient, zpow_negSucc, inv_pow, one_div]
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  calc
    _ ≤ ∑' z : ℤ, ∫⁻ x in (2 : ℝ)^z • annulus C,
        f x * gaussian x ∂(μHE[q+p] : Measure E) := by
      conv_lhs => rw [cone_eq_iUnion_annulus hcone hzero]
      exact lintegral_iUnion_le _ _
    _ ≤ ∑' z : ℤ, ENNReal.ofReal (dyadicCoefficient q z) * I := ENNReal.tsum_le_tsum hb
    _ = (∑' z : ℤ, ENNReal.ofReal (dyadicCoefficient q z)) * I := ENNReal.tsum_mul_right
    _ < ⊤ := ENNReal.mul_lt_top (tsum_dyadicCoefficient_lt_top hq) hfinite

#print axioms gaussian_pos
#print axioms gaussian_le_one
#print axioms gaussian_le_of_norm
#print axioms norm_lower_of_mem_scaled_annulus
#print axioms measurableSet_annulus
#print axioms gaussian_scaled_annular_bound
#print axioms gaussian_lintegral_lt_top
#assert_trust kernel gaussian_pos
#assert_trust kernel gaussian_le_one
#assert_trust kernel gaussian_le_of_norm
#assert_trust kernel norm_lower_of_mem_scaled_annulus
#assert_trust kernel measurableSet_annulus
#assert_trust kernel gaussian_scaled_annular_bound
#assert_trust kernel gaussian_lintegral_lt_top
end NLA.Proofs.TR06.HomogeneousGaussian
