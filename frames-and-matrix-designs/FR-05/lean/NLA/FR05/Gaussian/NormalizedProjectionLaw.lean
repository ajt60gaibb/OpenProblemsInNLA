import NLA.FR05.Gaussian.SimplexProjectionLaw
import NLA.FR05.Gaussian.GaussianSphere

/-!
# Normalised Gaussian projections and Haar sphere projections

The sections develop `NormalizedProjectionLaw`, `HaarSphereProjection`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section NormalizedProjectionLaw

open MeasureTheory ProbabilityTheory Matrix Set
open scoped ENNReal BigOperators


def normalizedGaussianHead (p : ℝ × Signal 2) : Signal 2 :=
  fun i ↦ (((Real.sqrt (signalEnergy p.2 + p.1))⁻¹ : ℝ) : ℂ) * p.2 i

@[fun_prop]
theorem measurable_normalizedGaussianHead : Measurable normalizedGaussianHead := by
  unfold normalizedGaussianHead signalEnergy squaredEuclideanNorm
  fun_prop

theorem normalizedGaussianHead_phaseVector (s : ℝ) (r : Fin 2 → ℝ)
    (hr : ∀ i, 0 ≤ r i) (θ : Fin 2 → ConePhase) :
    normalizedGaussianHead (s, phaseVectorMap (r, θ)) =
      phaseVectorMap (normalizedMagnitudes (s, r), θ) := by
  have he : signalEnergy (phaseVectorMap (r, θ)) = r 0 + r 1 := by
    simp [signalEnergy, squaredEuclideanNorm, Fin.sum_univ_two, phaseVectorMap_normSq _ _ hr]
  ext i
  simp only [normalizedGaussianHead, he, phaseVectorMap, normalizedMagnitudes,
    Real.sqrt_div (hr i), Complex.ofReal_div, Complex.ofReal_inv]
  ring

theorem normalizedGaussianHead_law (n : ℕ) :
    ((gammaMeasure (n + 1) 1).prod (standardComplexGaussianTail 2)).map
      normalizedGaussianHead = sphereProjectionLaw n := by
  let γ := gammaMeasure (n + 1) 1
  let : IsProbabilityMeasure γ := isProbabilityMeasure_gammaMeasure (by positivity) zero_lt_one
  let H : (ℝ × (Fin 2 → ℝ)) × (Fin 2 → ConePhase) → Signal 2 :=
    fun p ↦ normalizedGaussianHead (p.1.1, phaseVectorMap (p.1.2, p.2))
  have hH : Measurable H := by unfold H; fun_prop
  have hp : γ.prod (standardComplexGaussianTail 2) =
      (γ.prod (magnitudeGaussianLaw.prod phaseVectorLaw)).map (Prod.map id phaseVectorMap) := by
    rw [← Measure.map_prod_map _ _ measurable_id continuous_phaseVectorMap.measurable,
      Measure.map_id, ← standardComplexGaussianTail_two_polar]
  have hstart : (γ.prod (standardComplexGaussianTail 2)).map normalizedGaussianHead =
      ((γ.prod magnitudeGaussianLaw).prod phaseVectorLaw).map H := by
    rw [hp, Measure.map_map measurable_normalizedGaussianHead (by fun_prop),
      ← Measure.prodAssoc_prod (μ := γ) (ν := magnitudeGaussianLaw) (τ := phaseVectorLaw),
      Measure.map_map (measurable_normalizedGaussianHead.comp (by fun_prop))
        MeasurableEquiv.prodAssoc.measurable]
    rfl
  change (γ.prod (standardComplexGaussianTail 2)).map normalizedGaussianHead = _
  rw [hstart, sphereProjectionLaw_eq_polar]
  have he : ((γ.prod magnitudeGaussianLaw).prod phaseVectorLaw).map H =
      ((γ.prod magnitudeGaussianLaw).prod phaseVectorLaw).map
        (phaseVectorMap ∘ Prod.map normalizedMagnitudes id) := by
    apply Measure.map_congr
    have hr : ∀ᵐ p ∂γ.prod magnitudeGaussianLaw, ∀ i, 0 ≤ p.2 i :=
      Measure.quasiMeasurePreserving_snd.ae ae_magnitudeGaussianLaw_nonneg
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hr] with p hp
    exact normalizedGaussianHead_phaseVector p.1.1 p.1.2 hp p.2
  rw [he, ← Measure.map_map continuous_phaseVectorMap.measurable
    (measurable_normalizedMagnitudes.prodMap measurable_id),
    ← Measure.map_prod_map _ _ measurable_normalizedMagnitudes measurable_id,
    Measure.map_id, gamma_pair_normalizedMagnitudes]

def normalizedFirstTwo {m : ℕ} (hm : 2 ≤ m) (z : Signal m) : Signal 2 :=
  fun i ↦ normalizedComplexVector z (Fin.castLE hm i)

@[fun_prop]
theorem measurable_normalizedFirstTwo {m : ℕ} (hm : 2 ≤ m) :
    Measurable (normalizedFirstTwo hm) := by
  unfold normalizedFirstTwo
  exact measurable_pi_lambda _ fun i ↦
    (measurable_pi_apply (Fin.castLE hm i)).comp (measurable_normalizedComplexVector m)

theorem normalizedFirstTwo_gaussian_law (n : ℕ) :
    (standardComplexGaussianTail (2 + (n + 1))).map
      (normalizedFirstTwo (by lia)) = sphereProjectionLaw n := by
  let F : Signal 2 × Signal (n + 1) → ℝ × Signal 2 :=
    fun p ↦ (signalEnergy p.2, p.1)
  have hF : Measurable F := by
    apply Continuous.measurable
    unfold F signalEnergy squaredEuclideanNorm
    fun_prop
  have he : normalizedFirstTwo (by lia : 2 ≤ 2 + (n + 1)) =
      normalizedGaussianHead ∘ F ∘ splitGaussianSum 2 (n + 1) := by
    funext z
    ext i
    simp only [normalizedFirstTwo, normalizedComplexVector, Function.comp_apply,
      normalizedGaussianHead, F, signalEnergy_splitSum]
    rfl
  rw [he, ← Measure.map_map measurable_normalizedGaussianHead
    (hF.comp (continuous_splitGaussianSum 2 (n + 1)).measurable),
    ← Measure.map_map hF (continuous_splitGaussianSum 2 (n + 1)).measurable,
    standardComplexGaussianTail_map_splitSum]
  have hsplit : ((standardComplexGaussianTail 2).prod
      (standardComplexGaussianTail (n + 1))).map F =
      (gammaMeasure (n + 1) 1).prod (standardComplexGaussianTail 2) := by
    have hmap := Measure.map_prod_map (standardComplexGaussianTail (n + 1))
      (standardComplexGaussianTail 2)
      (show Measurable (signalEnergy (n := n + 1)) by
        apply Continuous.measurable; unfold signalEnergy squaredEuclideanNorm; fun_prop)
      measurable_id
    rw [standardComplexGaussianTail_map_energy (by lia), Measure.map_id] at hmap
    simp only [Nat.cast_add, Nat.cast_one] at hmap
    have hswap : ((standardComplexGaussianTail 2).prod
        (standardComplexGaussianTail (n + 1))).map Prod.swap =
        (standardComplexGaussianTail (n + 1)).prod (standardComplexGaussianTail 2) :=
      Measure.prod_swap
    rw [hmap, ← hswap, Measure.map_map (by
        apply Measurable.prodMap
        · apply Continuous.measurable; unfold signalEnergy squaredEuclideanNorm; fun_prop
        · exact measurable_id) measurable_swap]
    rfl
  rw [hsplit, normalizedGaussianHead_law]

end NormalizedProjectionLaw

section HaarSphereProjection

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

theorem normalizedFirstTwo_gaussian_law_of_le {m : ℕ} (hm : 3 ≤ m) :
    (standardComplexGaussianTail m).map (normalizedFirstTwo (by lia)) =
      sphereProjectionLaw (m - 3) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = 2 + (n + 1) := ⟨m - 3, by lia⟩
  simpa only [show 2 + (n + 1) - 3 = n by lia] using normalizedFirstTwo_gaussian_law n

theorem normalizedGaussian_orthonormal_projection {m : ℕ} (hm : 3 ≤ m)
    (B : Matrix (Fin m) (Fin 2) ℂ) (hB : Bᴴ * B = 1) :
    (standardComplexGaussianTail m).map (fun z ↦ Bᴴ *ᵥ normalizedComplexVector z) =
      sphereProjectionLaw (m - 3) := by
  obtain ⟨U, hU⟩ := exists_sourceUnitary_extension (by lia : 2 ≤ m) B hB
  have he : (fun z ↦ Bᴴ *ᵥ normalizedComplexVector z) =
      normalizedFirstTwo (by lia : 2 ≤ m) ∘ (fun z ↦ (star U).val *ᵥ z) := by
    funext z
    ext i
    change _ = normalizedComplexVector ((star U).val *ᵥ z) (Fin.castLE (by lia) i)
    rw [normalizedComplexVector_unitary_mulVec]
    change (∑ j, star (B j i) * normalizedComplexVector z j) =
      ∑ j, star (U.val j (Fin.castLE (by lia) i)) * normalizedComplexVector z j
    simp_rw [hU]
  rw [he, ← Measure.map_map (measurable_normalizedFirstTwo _) (by fun_prop),
    standardComplexGaussianTail_map_unitary_mulVec (star U).val
      (Matrix.UnitaryGroup.star_mul_self (star U)),
    normalizedFirstTwo_gaussian_law_of_le hm]

def sourceHaarFirstTwoCoordinates {m : ℕ} (hm : 2 ≤ m) (U : SourceUnitary m) : Signal 2 :=
  fun i ↦ U.val (Fin.castLE hm i) ⟨0, by lia⟩

@[fun_prop]
theorem continuous_sourceHaarFirstTwoCoordinates {m : ℕ} (hm : 2 ≤ m) :
    Continuous (sourceHaarFirstTwoCoordinates hm) := by
  exact continuous_pi fun i ↦
    ((continuous_apply (Fin.castLE hm i)).comp (continuous_sourceHaarFirstColumn (by lia)))

theorem sourceHaarFirstTwoCoordinates_law {m : ℕ} (hm : 3 ≤ m) :
    (sourceUnitaryLaw m).map (sourceHaarFirstTwoCoordinates (by lia)) =
      sphereProjectionLaw (m - 3) := by
  have h := congrArg (Measure.map (fun z : Signal m ↦ fun i : Fin 2 ↦
      z (Fin.castLE (by lia : 2 ≤ m) i)))
    (sourceHaarFirstColumn_eq_normalizedGaussian (by lia : 0 < m))
  rw [Measure.map_map (by fun_prop) (continuous_sourceHaarFirstColumn _).measurable,
    Measure.map_map (by fun_prop) (measurable_normalizedComplexVector m)] at h
  exact h.trans (normalizedFirstTwo_gaussian_law_of_le hm)

end HaarSphereProjection

end NLA.FR05
