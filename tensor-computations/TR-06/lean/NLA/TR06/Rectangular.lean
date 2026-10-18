/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/
import NLA.TR06.NormDet

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped ENNReal MeasureTheory NNReal
open MeasureTheory Set Function

namespace NLA.TR06.Area

section Hausdorff
variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {K : ℝ≥0} {f : X → Y} {s : Set X}

/-- The normalized Euclidean Hausdorff measure has the usual Lipschitz bound. -/
theorem euclidean_image_le_of_lipschitzOn (h : LipschitzOnWith K f s) (m : ℕ) :
    μHE[m] (f '' s) ≤ (K : ℝ≥0∞) ^ m * μHE[m] s := by
  have h' := h.hausdorffMeasure_image_le (show (0 : ℝ) ≤ m by positivity)
  simp only [ENNReal.rpow_natCast] at h'
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
    Measure.nnreal_smul_coe_apply]
  calc
    _ ≤ _ * ((K : ℝ≥0∞) ^ m * μH[(m : ℝ)] s) := by gcongr
    _ = _ := by ring

/-- Anti-Lipschitz lower bound, in Euclidean normalization. -/
theorem euclidean_le_image_of_antilipschitz (h : AntilipschitzWith K f) (m : ℕ) :
    μHE[m] s ≤ (K : ℝ≥0∞) ^ m * μHE[m] (f '' s) := by
  have h' := h.le_hausdorffMeasure_image (show (0 : ℝ) ≤ m by positivity) s
  simp only [ENNReal.rpow_natCast] at h'
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
    Measure.nnreal_smul_coe_apply]
  calc
    _ ≤ _ * ((K : ℝ≥0∞) ^ m * μH[(m : ℝ)] (f '' s)) := by gcongr
    _ = _ := by ring

/-- A lower bound also applies to a map restricted to an arbitrary subset. -/
theorem euclidean_le_image_of_antilipschitzOn
    (h : AntilipschitzWith K (s.domRestrict f)) (m : ℕ) :
    μHE[m] s ≤ (K : ℝ≥0∞) ^ m * μHE[m] (f '' s) := by
  have h' := euclidean_le_image_of_antilipschitz (s := Set.univ) h m
  have hsource : (μHE[m] : Measure s) Set.univ = (μHE[m] : Measure X) s := by
    have hval := (isometry_subtype_coe : Isometry (Subtype.val : s → X)).euclideanHausdorffMeasure_image (d := m) Set.univ
    simpa only [Set.image_univ, Subtype.range_coe_subtype, ofPred_mem_eq] using hval.symm
  have himage : s.domRestrict f '' Set.univ = f '' s := by
    ext y
    simp only [mem_image, mem_univ, true_and, domRestrict_apply, Subtype.exists, exists_prop]
  rw [hsource, himage] at h'
  exact h'

end Hausdorff

section Approximation
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {A : E →L[ℝ] F} {f : E → F} {s : Set E} {δ K : ℝ≥0}

/-- After reparameterization by an injective linear map, the approximation
error becomes a relative metric error. No inverse on the full codomain is used. -/
theorem approximation_image_norm_bounds
    (hA : Injective A) (hK : AntilipschitzWith K A)
    (hf : ApproximatesLinearOn f A s δ)
    {x y : F} (hx : x ∈ A '' s) (hy : y ∈ A '' s) :
    (1 - (δ : ℝ) * K) * ‖x - y‖ ≤
        ‖f (invFun A x) - f (invFun A y)‖ ∧
    ‖f (invFun A x) - f (invFun A y)‖ ≤
        (1 + (δ : ℝ) * K) * ‖x - y‖ := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  rw [(leftInverse_invFun hA) a, (leftInverse_invFun hA) b]
  have herror := hf a ha b hb
  have hdist : ‖a - b‖ ≤ (K : ℝ) * ‖A a - A b‖ := by
    simpa only [dist_eq_norm] using hK.le_mul_dist a b
  have he : ‖f a - f b - (A a - A b)‖ ≤ (δ : ℝ) * K * ‖A a - A b‖ := by
    rw [map_sub] at herror
    nlinarith [mul_le_mul_of_nonneg_left hdist (show (0 : ℝ) ≤ δ from δ.2)]
  constructor
  · have htri : ‖A a - A b‖ ≤ ‖f a - f b‖ + ‖f a - f b - (A a - A b)‖ := by
      exact norm_le_norm_add_norm_sub (f a - f b) (A a - A b)
    nlinarith
  · have htri : ‖f a - f b‖ ≤ ‖A a - A b‖ + ‖f a - f b - (A a - A b)‖ :=
      by simpa only [norm_sub_rev] using (norm_le_norm_add_norm_sub (A a - A b) (f a - f b))
    nlinarith

/-- Upper metric bound on the reparameterized image. -/
theorem approximation_image_lipschitz
    (hA : Injective A) (hK : AntilipschitzWith K A)
    (hf : ApproximatesLinearOn f A s δ) :
    LipschitzOnWith (1 + δ * K) (fun x => f (invFun A x)) (A '' s) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simpa only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul] using
    (approximation_image_norm_bounds hA hK hf hx hy).2

/-- Lower metric bound on the reparameterized image. -/
theorem approximation_image_antilipschitz
    (hA : Injective A) (hK : AntilipschitzWith K A)
    (hf : ApproximatesLinearOn f A s δ) (hδ : δ * K < 1) :
    AntilipschitzWith (1 - δ * K)⁻¹
      (fun x : A '' s => f (invFun A x.val)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have h := (approximation_image_norm_bounds hA hK hf x.property y.property).1
  have hpos : 0 < (1 : ℝ) - δ * K := by exact sub_pos.mpr (show (δ : ℝ) * K < 1 by exact_mod_cast hδ)
  rw [Subtype.dist_eq, dist_eq_norm, dist_eq_norm, NNReal.coe_inv,
    NNReal.coe_sub hδ.le, NNReal.coe_one, NNReal.coe_mul]
  exact (le_inv_mul_iff₀ hpos).2 h

end Approximation

section Volume
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {A : E →L[ℝ] F} {f : E → F} {s : Set E} {δ K : ℝ≥0}

/-- Upper rectangular volume estimate near an injective linear map. -/
theorem approximation_euclidean_image_le
    (hA : Injective A) (hK : AntilipschitzWith K A)
    (hf : ApproximatesLinearOn f A s δ) :
    μHE[Module.finrank ℝ E] (f '' s) ≤
      ((1 + δ * K : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E *
        (ENNReal.ofReal A.toLinearMap.normDet * volume s) := by
  have h := euclidean_image_le_of_lipschitzOn
    (approximation_image_lipschitz hA hK hf) (Module.finrank ℝ E)
  have himage : (fun x => f (invFun A x)) '' (A '' s) = f '' s := by
    rw [image_image]
    congr 1
    funext x
    rw [leftInverse_invFun hA x]
  rw [himage] at h
  have hlinear : μHE[Module.finrank ℝ E] (A '' s) =
      ENNReal.ofReal A.toLinearMap.normDet * volume s :=
    A.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume s
  rw [hlinear] at h
  exact h

/-- Lower rectangular volume estimate, in a form valid also for infinite volume. -/
theorem approximation_le_euclidean_image
    (hA : Injective A) (hK : AntilipschitzWith K A)
    (hf : ApproximatesLinearOn f A s δ) (hδ : δ * K < 1) :
    ENNReal.ofReal A.toLinearMap.normDet * volume s ≤
      (((1 - δ * K)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E *
        μHE[Module.finrank ℝ E] (f '' s) := by
  have h := euclidean_le_image_of_antilipschitzOn
    (s := A '' s) (f := fun x => f (invFun A x))
    (approximation_image_antilipschitz hA hK hf hδ) (Module.finrank ℝ E)
  have himage : (fun x => f (invFun A x)) '' (A '' s) = f '' s := by
    rw [image_image]
    congr 1
    funext x
    rw [leftInverse_invFun hA x]
  rw [himage] at h
  have hlinear : μHE[Module.finrank ℝ E] (A '' s) =
      ENNReal.ofReal A.toLinearMap.normDet * volume s :=
    A.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume s
  rw [hlinear] at h
  exact h

/-- Symmetric sandwich lower bound with no divisions by a measured set. -/
theorem approximation_euclidean_image_lower
    (hA : Injective A) (hK : AntilipschitzWith K A)
    (hf : ApproximatesLinearOn f A s δ) (hδ : δ * K < 1) :
    ((1 - δ * K : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E *
        (ENNReal.ofReal A.toLinearMap.normDet * volume s) ≤
      μHE[Module.finrank ℝ E] (f '' s) := by
  have hq : (1 - δ * K : ℝ≥0) ≠ 0 := ne_of_gt (tsub_pos_of_lt hδ)
  have h := approximation_le_euclidean_image hA hK hf hδ
  rw [ENNReal.coe_inv hq, ← ENNReal.inv_pow] at h
  have hzero : (((1 - δ * K : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E)⁻¹ ≠ 0 := by simp
  have htop : (((1 - δ * K : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E)⁻¹ ≠ ⊤ := by
    apply ENNReal.inv_ne_top.mpr
    exact pow_ne_zero _ (ENNReal.coe_ne_zero.mpr hq)
  have hh := (ENNReal.inv_mul_le_iff hzero htop).mpr h
  simpa only [inv_inv] using hh

end Volume

#print axioms approximation_euclidean_image_lower
#assert_trust kernel approximation_euclidean_image_lower
#print axioms approximation_euclidean_image_le
#print axioms approximation_le_euclidean_image
#assert_trust kernel approximation_euclidean_image_le
#assert_trust kernel approximation_le_euclidean_image

#print axioms euclidean_image_le_of_lipschitzOn
#print axioms approximation_image_norm_bounds
#print axioms approximation_image_antilipschitz
#assert_trust kernel euclidean_image_le_of_lipschitzOn
#assert_trust kernel approximation_image_norm_bounds
#assert_trust kernel approximation_image_antilipschitz

end NLA.TR06.Area
