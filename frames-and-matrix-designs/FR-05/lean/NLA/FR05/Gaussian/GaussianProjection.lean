/-
The exact one-dimensional law of a standard complex-Gaussian projection.

This bridges the explicit two-real-coordinate realization used by
`PlantedLaw.lean` to the `gaussianReal` interval estimates used in the first
branch of Lemma 3.6.  In particular, it does not replace the source law by a
surrogate: the result is about `standardComplexGaussianTail` itself.
-/
import NLA.FR05.Densities.PlantedLaw
import NLA.FR05.Planted.Jacobian

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators ComplexConjugate RealInnerProductSpace

namespace NLA.FR05

/-- Real coordinate vector representing the complex linear functional
`w ↦ Re (w^* z)`. -/
def tailGaussianCoefficients {n : ℕ} (z : Signal n) : (Fin n × Fin 2) → ℝ :=
  fun jk ↦ if jk.2 = 0 then (z jk.1).re / Real.sqrt 2 else (z jk.1).im / Real.sqrt 2

/-- The continuous real linear functional associated to a tail direction. -/
def tailGaussianFunctional {n : ℕ} (z : Signal n) :
    EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ :=
  innerSL ℝ (toLp 2 (tailGaussianCoefficients z))

theorem tailGaussianFunctional_apply {n : ℕ} (z : Signal n)
    (x : (Fin n × Fin 2) → ℝ) :
    tailGaussianFunctional z (toLp 2 x) =
      (star (standardComplexTail x) ⬝ᵥ z).re := by
  unfold tailGaussianFunctional
  rw [innerSL_apply_apply]
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, Pi.star_apply, star_trivial]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [tailGaussianCoefficients, standardComplexTail]
  ring

theorem tailGaussianCoefficients_energy {n : ℕ} (z : Signal n) :
    ∑ jk, (tailGaussianCoefficients z jk) ^ 2 = signalEnergy z / 2 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  simp only [tailGaussianCoefficients]
  simp only [ite_true]
  simp only [if_neg (show (1 : Fin 2) ≠ 0 by decide)]
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  unfold signalEnergy squaredEuclideanNorm
  simp only [Complex.normSq_apply]
  simp only [div_pow]
  change (∑ j : Fin n, ((z j).re ^ 2 / (Real.sqrt 2) ^ 2 +
      (z j).im ^ 2 / (Real.sqrt 2) ^ 2)) =
    (∑ j : Fin n, ((z j).re * (z j).re + (z j).im * (z j).im)) / 2
  rw [hsqrt]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem tailGaussianFunctional_normSq {n : ℕ} (z : Signal n) :
    ‖tailGaussianFunctional z‖ ^ 2 = signalEnergy z / 2 := by
  rw [tailGaussianFunctional, innerSL_apply_norm,
    EuclideanSpace.real_norm_sq_eq]
  exact tailGaussianCoefficients_energy z

/-- Measurability of the real complex-Gaussian projection. -/
theorem measurable_real_star_dotProduct {n : ℕ} (z : Signal n) :
    Measurable (fun w : Signal n ↦ (star w ⬝ᵥ z).re) := by
  unfold dotProduct
  have hsum : Measurable (fun w : Signal n ↦
      ∑ i, (star (w i) * z i).re) :=
    Finset.measurable_sum _ (by fun_prop)
  simpa only [Pi.star_apply, Complex.re_sum] using hsum

/-- The exact Gaussian law of a real complex-Gaussian projection. -/
theorem standardComplexGaussianTail_map_real_dotProduct {n : ℕ} (z : Signal n) :
    (standardComplexGaussianTail n).map (fun w ↦ (star w ⬝ᵥ z).re) =
      gaussianReal 0 (signalEnergy z / 2).toNNReal := by
  let μ : Measure ((Fin n × Fin 2) → ℝ) :=
    Measure.pi (fun _ : Fin n × Fin 2 ↦ gaussianReal 0 1)
  let L : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ :=
    tailGaussianFunctional z
  have hmap : μ.map (toLp 2) = stdGaussian (EuclideanSpace ℝ (Fin n × Fin 2)) := by
    exact map_pi_eq_stdGaussian
  calc
    (standardComplexGaussianTail n).map (fun w ↦ (star w ⬝ᵥ z).re) =
        (μ.map standardComplexTail).map (fun w ↦ (star w ⬝ᵥ z).re) := by rfl
    _ = μ.map ((fun w ↦ (star w ⬝ᵥ z).re) ∘ standardComplexTail) := by
      rw [Measure.map_map (measurable_real_star_dotProduct z)
        (measurable_standardComplexGaussianTail_map (n := n))]
    _ = μ.map (L ∘ toLp 2) := by
      congr 1
      funext x
      exact (tailGaussianFunctional_apply z x).symm
    _ = (μ.map (toLp 2)).map L := by
      rw [Measure.map_map L.continuous.measurable (WithLp.measurable_toLp 2 _)]
    _ = (stdGaussian (EuclideanSpace ℝ (Fin n × Fin 2))).map L := by
      rw [hmap]
    _ = gaussianReal 0 (signalEnergy z / 2).toNNReal := by
      rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
        variance_dual_stdGaussian, tailGaussianFunctional_normSq]

/-- The exact projection law as a measure-preserving map, for transporting
measurable events without repeating pushforward calculations. -/
theorem measurePreserving_real_star_dotProduct {n : ℕ} (z : Signal n) :
    MeasurePreserving (fun w : Signal n ↦ (star w ⬝ᵥ z).re)
      (standardComplexGaussianTail n) (gaussianReal 0 (signalEnergy z / 2).toNNReal) :=
  ⟨measurable_real_star_dotProduct z, standardComplexGaussianTail_map_real_dotProduct z⟩

/-- The underlying phase-rotation identity, stated independently of a
planted row so it can be used while conditioning on the scalar coordinates. -/
theorem phaseRotate_real_dotProduct {n : ℕ} (α : ℝ) (w z : Signal n) :
    (star (Complex.exp ((-α : ℂ) * Complex.I) • w) ⬝ᵥ z).re =
      (star w ⬝ᵥ (Complex.exp ((α : ℂ) * Complex.I) • z)).re := by
  rw [star_smul, smul_dotProduct, dotProduct_smul]
  have hphase : star (Complex.exp ((-α : ℂ) * Complex.I)) =
      Complex.exp ((α : ℂ) * Complex.I) := by
    change conj (Complex.exp ((-α : ℂ) * Complex.I)) = _
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hphase]

/-- Move the planted first-phase rotation from the Gaussian tail to the
deterministic direction in the scalar projection. -/
theorem phaseNormalizedTail_real_dotProduct {n : ℕ} (r : PlantedRow n)
    (z : Signal n) :
    (star (phaseNormalizedTail r) ⬝ᵥ z).re =
      (star r.tail ⬝ᵥ (Complex.exp ((r.phaseOne : ℂ) * Complex.I) • z)).re :=
  phaseRotate_real_dotProduct r.phaseOne r.tail z

/-- Phase rotation preserves the explicit squared Euclidean tail energy. -/
theorem signalEnergy_phaseRotate {n : ℕ} (α : ℝ) (z : Signal n) :
    signalEnergy (Complex.exp ((α : ℂ) * Complex.I) • z) = signalEnergy z := by
  unfold signalEnergy squaredEuclideanNorm
  apply Finset.sum_congr rfl
  intro j hj
  change Complex.normSq (Complex.exp ((α : ℂ) * Complex.I) * z j) =
    Complex.normSq (z j)
  rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  norm_num

end NLA.FR05
