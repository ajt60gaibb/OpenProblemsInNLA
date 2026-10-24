/-
Copyright (c) 2026. Released under Apache 2.0 license.
Actual scalar change of variables for the Euclidean Hausdorff measure.
-/
import Mathlib
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal NNReal Pointwise
open MeasureTheory Set

namespace NLA.Proofs.TR06.HomogeneousGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Positive scalar multiplication preserves Hausdorff measure after the
literal dimension-dependent rescaling of its source measure. -/
theorem measurePreserving_scale (k : ℕ) {t : ℝ} (ht : 0 < t) :
    MeasurePreserving (fun x : E => t • x)
      (ENNReal.ofReal (t ^ k) • (μHE[k] : Measure E)) μHE[k] := by
  refine ⟨by fun_prop, ?_⟩
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.smul_apply]
  have hp := euclideanHausdorffMeasure_homothety_preimage (𝕜 := ℝ) k (0 : E)
    (ne_of_gt ht) s
  have he : (AffineMap.homothety (0 : E) t : E → E) = (fun x : E => t • x) := by
    funext x
    simp [AffineMap.homothety_apply]
  rw [he] at hp
  rw [hp]
  simp only [ENNReal.smul_def, smul_eq_mul]
  have hn : ‖t‖₊ ≠ 0 := by simpa using ne_of_gt ht
  have hc : ENNReal.ofReal (t ^ k) * ((‖t‖₊⁻¹ ^ k : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [ENNReal.ofReal_pow ht.le]
    have heq : ENNReal.ofReal t = (‖t‖₊ : ℝ≥0∞) := by
      simp [Real.nnnorm_of_nonneg ht.le, ENNReal.ofReal_eq_coe_nnreal ht.le]
    rw [heq, ← ENNReal.coe_pow, ← ENNReal.coe_mul, ← mul_pow,
      mul_inv_cancel₀ hn, one_pow, ENNReal.coe_one]
  rw [← mul_assoc, hc, one_mul]

/-- Exact set-integral change of variables; measurability of the integrand
is unnecessary because the actual scalar map is a measurable equivalence. -/
theorem lintegral_scaled_set (k : ℕ) {t : ℝ} (ht : 0 < t)
    (s : Set E) (f : E → ℝ≥0∞) :
    (∫⁻ x in t • s, f x ∂(μHE[k] : Measure E)) =
      ENNReal.ofReal (t ^ k) * ∫⁻ x in s, f (t • x) ∂(μHE[k] : Measure E) := by
  have h := (measurePreserving_scale (E := E) k ht).setLIntegral_comp_emb
    (Homeomorph.smulOfNeZero t (ne_of_gt ht)).toMeasurableEquiv.measurableEmbedding f s
  simpa only [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
    Homeomorph.smulOfNeZero_apply, Set.image_smul] using h.symm

/-- The fixed reference annulus is chosen half open to allow disjoint dilates. -/
def annulus (C : Set E) : Set E := C ∩ {x | 1 ≤ ‖x‖ ∧ ‖x‖ < 2}

/-- Positive scaling invariance, expressed as an exact membership equivalence. -/
def PositiveCone (C : Set E) : Prop := ∀ t : ℝ, 0 < t → ∀ x : E, t • x ∈ C ↔ x ∈ C

#print axioms measurePreserving_scale
#print axioms lintegral_scaled_set
#assert_trust kernel measurePreserving_scale
#assert_trust kernel lintegral_scaled_set

end NLA.Proofs.TR06.HomogeneousGaussian
