import NLA.FR05.Overlap.UnitaryCompletion
import NLA.FR05.Gaussian.GaussianQuadraticIntegral

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Elementwise

namespace NLA.FR05


def normalizedComplexVector {n : ℕ} (z : Signal n) : Signal n :=
  fun i ↦ (((Real.sqrt (signalEnergy z))⁻¹ : ℝ) : ℂ) * z i

@[fun_prop]
theorem measurable_normalizedComplexVector (n : ℕ) :
    Measurable (normalizedComplexVector (n := n)) := by
  unfold normalizedComplexVector signalEnergy squaredEuclideanNorm
  fun_prop

theorem signalEnergy_real_mul {n : ℕ} (r : ℝ) (z : Signal n) :
    signalEnergy (fun i ↦ (r : ℂ) * z i) = r ^ 2 * signalEnergy z := by
  simp [signalEnergy, squaredEuclideanNorm, Complex.normSq_mul,
    Complex.normSq_ofReal, Finset.mul_sum, pow_two]

theorem signalEnergy_normalizedComplexVector {n : ℕ} {z : Signal n}
    (hz : 0 < signalEnergy z) :
    signalEnergy (normalizedComplexVector z) = 1 := by
  unfold normalizedComplexVector
  rw [signalEnergy_real_mul, inv_pow,
    Real.sq_sqrt hz.le, inv_mul_cancel₀ hz.ne']

theorem signalEnergy_unitary_mulVec {n : ℕ} (U : SourceUnitary n) (z : Signal n) :
    signalEnergy (U.val *ᵥ z) = signalEnergy z := by
  rw [signalEnergy_mulVec_eq_gram,
    show U.valᴴ * U.val = 1 from Matrix.UnitaryGroup.star_mul_self U,
    Matrix.one_mulVec, signalEnergy_eq_star_dotProduct]

theorem normalizedComplexVector_unitary_mulVec {n : ℕ}
    (U : SourceUnitary n) (z : Signal n) :
    normalizedComplexVector (U.val *ᵥ z) = U.val *ᵥ normalizedComplexVector z := by
  unfold normalizedComplexVector
  rw [signalEnergy_unitary_mulVec]
  exact (Matrix.mulVec_smul U.val
    (((Real.sqrt (signalEnergy z))⁻¹ : ℝ) : ℂ) z).symm

theorem ae_standardComplexGaussian_energy_pos {n : ℕ} (hn : 0 < n) :
    ∀ᵐ z ∂standardComplexGaussianTail n, 0 < signalEnergy z := by
  let i : Fin n := ⟨0, hn⟩
  have hmap : (standardComplexGaussianTail n).map (fun z ↦ Complex.normSq (z i)) =
      expMeasure 1 := by
    rw [← scalarComplexGaussian_map_normSq,
      ← (measurePreserving_eval (fun _ : Fin n ↦ scalarComplexGaussian) i).map_eq,
      ← standardComplexGaussianTail_eq_pi n, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hne : ∀ᵐ s ∂expMeasure 1, s ≠ 0 := by
    rw [ae_iff]
    simpa only [expMeasure, gammaMeasure, not_not, Set.ofPred_eq_eq_singleton] using
      withDensity_absolutelyContinuous volume (gammaPDF 1 1) (measure_singleton (0 : ℝ))
  have hpos : ∀ᵐ z ∂standardComplexGaussianTail n, Complex.normSq (z i) ≠ 0 := by
    rw [← hmap] at hne
    exact (ae_map_iff (f := fun z : Signal n ↦ Complex.normSq (z i))
      (by apply Continuous.aemeasurable; fun_prop) (measurableSet_singleton 0).compl).mp hne
  filter_upwards [hpos] with z hz
  exact (lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hz)).trans_le
    (Finset.single_le_sum (fun j _ ↦ Complex.normSq_nonneg (z j)) (Finset.mem_univ i))

def sourceHaarFirstColumn {n : ℕ} (hn : 0 < n) (U : SourceUnitary n) : Signal n :=
  fun i ↦ U.val i ⟨0, hn⟩

@[fun_prop]
theorem continuous_sourceHaarFirstColumn {n : ℕ} (hn : 0 < n) :
    Continuous (sourceHaarFirstColumn hn) := by
  exact continuous_pi fun i ↦ (continuous_apply (⟨0, hn⟩ : Fin n)).comp
    ((continuous_apply i).comp continuous_subtype_val)

theorem integral_haar_unitVector {n : ℕ} (hn : 0 < n) (v : Signal n)
    (hv : signalEnergy v = 1) (f : Signal n → ℝ) :
    (∫ U : SourceUnitary n, f (U.val *ᵥ v) ∂sourceUnitaryLaw n) =
      ∫ U : SourceUnitary n, f (sourceHaarFirstColumn hn U) ∂sourceUnitaryLaw n := by
  obtain ⟨V, hV⟩ := exists_sourceUnitary_firstColumn hn v hv
  have he (U : SourceUnitary n) :
      U.val *ᵥ v = sourceHaarFirstColumn hn (U * V) := by
    ext i
    simp only [sourceHaarFirstColumn, Submonoid.coe_mul, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, hV]
  simp_rw [he]
  exact integral_mul_right_eq_self (fun U ↦ f (sourceHaarFirstColumn hn U)) V

theorem normalizedComplexVector_map_unitary {n : ℕ} (U : SourceUnitary n) :
    ((standardComplexGaussianTail n).map normalizedComplexVector).map
      (fun z ↦ U.val *ᵥ z) =
      (standardComplexGaussianTail n).map normalizedComplexVector := by
  rw [Measure.map_map (by fun_prop) (measurable_normalizedComplexVector n)]
  have he : (fun z ↦ U.val *ᵥ normalizedComplexVector z) =
      (fun z ↦ normalizedComplexVector (U.val *ᵥ z)) := by
    funext z
    exact (normalizedComplexVector_unitary_mulVec U z).symm
  change (standardComplexGaussianTail n).map
    (fun z ↦ U.val *ᵥ normalizedComplexVector z) = _
  rw [he]
  change (standardComplexGaussianTail n).map
    (normalizedComplexVector ∘ (fun z ↦ U.val *ᵥ z)) = _
  rw [← Measure.map_map (measurable_normalizedComplexVector n) (by fun_prop),
    standardComplexGaussianTail_map_unitary_mulVec U.val
      (Matrix.UnitaryGroup.star_mul_self U)]

theorem sourceHaarFirstColumn_eq_normalizedGaussian {n : ℕ} (hn : 0 < n) :
    (sourceUnitaryLaw n).map (sourceHaarFirstColumn hn) =
      (standardComplexGaussianTail n).map normalizedComplexVector := by
  let γ := standardComplexGaussianTail n
  let ν := γ.map normalizedComplexVector
  let μ := sourceUnitaryLaw n
  let : IsProbabilityMeasure (μ.map (sourceHaarFirstColumn hn)) :=
    Measure.isProbabilityMeasure_map (continuous_sourceHaarFirstColumn hn).measurable.aemeasurable
  let : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_normalizedComplexVector n).aemeasurable
  have hnν : ∀ᵐ v ∂ν, signalEnergy v = 1 := by
    apply (ae_map_iff (measurable_normalizedComplexVector n).aemeasurable
      (by apply isClosed_eq _ continuous_const |>.measurableSet
          unfold signalEnergy squaredEuclideanNorm
          fun_prop)).mpr
    filter_upwards [ae_standardComplexGaussian_energy_pos hn] with z hz
    exact signalEnergy_normalizedComplexVector hz
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hc : Continuous (fun p : SourceUnitary n × Signal n ↦ f (p.1.val *ᵥ p.2)) := by
    apply f.continuous.comp
    apply continuous_pi
    intro i
    change Continuous (fun p : SourceUnitary n × Signal n ↦ ∑ j, p.1.val i j * p.2 j)
    have hU : Continuous (fun U : SourceUnitary n ↦ U.val) := continuous_subtype_val
    exact continuous_finsetSum _ fun j _ ↦
      ((((continuous_apply j).comp ((continuous_apply i).comp hU)).comp continuous_fst).mul
        ((continuous_apply j).comp continuous_snd))
  have hi : Integrable (fun p : SourceUnitary n × Signal n ↦ f (p.1.val *ᵥ p.2))
      (μ.prod ν) :=
    Integrable.of_bound hc.aestronglyMeasurable ‖f‖
      (Filter.Eventually.of_forall fun _ ↦ f.norm_coe_le_norm _)
  have hleft (U : SourceUnitary n) :
      (∫ v, f (U.val *ᵥ v) ∂ν) = ∫ v, f v ∂ν := by
    rw [← integral_map (by fun_prop) f.continuous.aestronglyMeasurable,
      normalizedComplexVector_map_unitary]
  have hright : (∫ v, ∫ U : SourceUnitary n, f (U.val *ᵥ v) ∂μ ∂ν) =
      ∫ U : SourceUnitary n, f (sourceHaarFirstColumn hn U) ∂μ := by
    calc
      _ = ∫ _ : Signal n, ∫ U : SourceUnitary n,
          f (sourceHaarFirstColumn hn U) ∂μ ∂ν := by
        apply integral_congr_ae
        filter_upwards [hnν] with v hv
        exact integral_haar_unitVector hn v hv f
      _ = _ := by simp
  rw [integral_map (continuous_sourceHaarFirstColumn hn).measurable.aemeasurable
    f.continuous.aestronglyMeasurable]
  change _ = ∫ v, f v ∂ν
  rw [← hright, ← integral_integral_swap hi]
  simp_rw [hleft]
  simp

end NLA.FR05
