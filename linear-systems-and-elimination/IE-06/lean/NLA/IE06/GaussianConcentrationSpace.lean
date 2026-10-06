import NLA.IE06.GaussianConcentration

/-! Exact isometric transport of Gaussian concentration to arbitrary finite
dimensional real inner product spaces. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
namespace NLA.IE06.GaussianConcentrationSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

theorem lipschitz_integrable {f : H → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    Integrable f (stdGaussian H) := by
  let e := (stdOrthonormalBasis ℝ H).repr.symm
  have hm : MeasurePreserving e
      (stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ H)))) (stdGaussian H) :=
    ⟨by fun_prop, stdGaussian_map e⟩
  have hl : LipschitzWith L (f ∘ e) := by simpa using hf.comp e.lipschitz
  exact (hm.integrable_comp hf.continuous.aestronglyMeasurable).mp
    (GaussianConcentration.lipschitz_integrable hl)

theorem lipschitz_upper_tail {f : H → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : ℝ) (hx : 0 < x) :
    stdGaussian H {z | (L:ℝ)*sqrt (2*x) < f z - ∫ w, f w ∂stdGaussian H} ≤
      ENNReal.ofReal (exp (-x)) := by
  let e := (stdOrthonormalBasis ℝ H).repr.symm
  have hm : MeasurePreserving e
      (stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ H)))) (stdGaussian H) :=
    ⟨by fun_prop, stdGaussian_map e⟩
  have hl : LipschitzWith L (f ∘ e) := by simpa using hf.comp e.lipschitz
  have hb := GaussianConcentration.lipschitz_upper_tail hl x hx
  have hi : (∫ z, (f ∘ e) z
      ∂stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ H)))) =
      ∫ w, f w ∂stdGaussian H :=
    hm.integral_comp e.toHomeomorph.measurableEmbedding f
  rw [hi] at hb
  have hset : MeasurableSet {z : H | (L:ℝ)*sqrt (2*x) <
      f z - ∫ w, f w ∂stdGaussian H} := by
    exact measurableSet_lt measurable_const (hf.continuous.measurable.sub measurable_const)
  nth_rw 1 [← hm.map_eq]
  rw [Measure.map_apply hm.measurable hset]
  exact hb

theorem lipschitz_lower_tail {f : H → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : ℝ) (hx : 0 < x) :
    stdGaussian H {z | (L:ℝ)*sqrt (2*x) < (∫ w, f w ∂stdGaussian H) - f z} ≤
      ENNReal.ofReal (exp (-x)) := by
  have h := lipschitz_upper_tail hf.neg x hx
  simpa only [Pi.neg_apply, integral_neg, neg_sub_neg] using h

theorem mean_le_of_upper_tail {f : H → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {B x : ℝ} (hx : 0 < x)
    (hsmall : 2*exp (-x) < 1)
    (hupper : stdGaussian H {z | B < f z} ≤ ENNReal.ofReal (exp (-x))) :
    (∫ w, f w ∂stdGaussian H) ≤ B+(L:ℝ)*sqrt (2*x) := by
  by_contra! hmean
  have hcover : (Set.univ : Set H) ⊆ {z | B < f z} ∪
      {z | (L:ℝ)*sqrt (2*x) < (∫ w, f w ∂stdGaussian H)-f z} := by
    intro z _
    by_cases hz : B < f z
    · exact Or.inl hz
    · exact Or.inr (by dsimp; linarith)
  have hlow := lipschitz_lower_tail hf x hx
  have hle : (1:ℝ≥0∞) ≤ ENNReal.ofReal (exp (-x))+ENNReal.ofReal (exp (-x)) := by
    calc
      _ = stdGaussian H Set.univ := (measure_univ).symm
      _ ≤ _ := (measure_mono hcover).trans
        ((measure_union_le _ _).trans (add_le_add hupper hlow))
  have hsum : ENNReal.ofReal (exp (-x))+ENNReal.ofReal (exp (-x)) < 1 := by
    rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<1)).mpr (by linarith)
  exact (not_lt_of_ge hle) hsum

#assert_trust kernel lipschitz_integrable
#assert_trust kernel lipschitz_upper_tail
#assert_trust kernel lipschitz_lower_tail
#assert_trust kernel mean_le_of_upper_tail
#print axioms lipschitz_integrable
#print axioms lipschitz_upper_tail
#print axioms lipschitz_lower_tail
#print axioms mean_le_of_upper_tail

end NLA.IE06.GaussianConcentrationSpace
