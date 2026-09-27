import NLA.FR05.Gaussian.GaussianTail
import NLA.FR05.Probability

/-!
# Product structure and symmetries of complex Gaussian coordinates

The scalar, vector, and frame laws agree with products of independent real
Gaussians. Conjugation and coordinate splitting preserve these laws. The
splitting lemmas allow empty blocks and are shared by the sphere-projection
and overlap arguments.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace NLA.FR05

/-- Flatten independent real Gaussian coordinates without changing their joint law. -/
theorem map_pi_uncurry {I J : Type*} [Fintype I] [Fintype J] :
    (Measure.pi (fun _ : I ↦ Measure.pi (fun _ : J ↦ gaussianReal 0 1))).map
      (fun a (p : I × J) ↦ a p.1 p.2) =
      Measure.pi (fun _ : I × J ↦ gaussianReal 0 1) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have he :
      (fun a (p : I × J) ↦ a p.1 p.2) ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun i ↦ Set.univ.pi (fun j ↦ s (i, j))) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    exact ⟨fun h i j ↦ h (i, j), fun h p ↦ h p.1 p.2⟩
  rw [he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  simp only [Fintype.prod_prod_type]

/-- Regroup the three real-coordinate indices into independent rows. -/
theorem map_pi_rows
    {I J K X : Type*} [Fintype I] [Fintype J] [Fintype K] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] :
    (Measure.pi (fun _ : I ↦ Measure.pi (fun _ : J × K ↦ μ))).map
      (fun a (p : (I × J) × K) ↦ a p.1.1 (p.1.2, p.2)) =
      Measure.pi (fun _ : (I × J) × K ↦ μ) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have hpre :
      (fun a (p : (I × J) × K) ↦ a p.1.1 (p.1.2, p.2)) ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun i ↦ Set.univ.pi (fun p : J × K ↦ s ((i, p.1), p.2))) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h i p
      exact h ((i, p.1), p.2)
    · intro h p
      exact h p.1.1 (p.1.2, p.2)
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  simp only [Fintype.prod_prod_type]

/-- The existing Gaussian frame law is exactly the product of its complex row laws. -/
theorem standardComplexGaussianFrame_eq_pi (m d : ℕ) :
    standardComplexGaussianFrame m d =
      Measure.pi (fun _ : Fin m ↦ standardComplexGaussianTail d) := by
  let μ : Measure ((Fin m × Fin d) × Fin 2 → ℝ) :=
    Measure.pi (fun _ ↦ gaussianReal 0 1)
  let ν : Measure (Fin m → (Fin d × Fin 2 → ℝ)) :=
    Measure.pi (fun _ ↦ Measure.pi (fun _ ↦ gaussianReal 0 1))
  let flatten : (Fin m → (Fin d × Fin 2 → ℝ)) →
      ((Fin m × Fin d) × Fin 2 → ℝ) :=
    fun a p ↦ a p.1.1 (p.1.2, p.2)
  let convertFrame : ((Fin m × Fin d) × Fin 2 → ℝ) → Frame m d :=
    fun x ↦ ((Real.sqrt 2)⁻¹ : ℝ) • realCoordinatesToComplexFrame (WithLp.toLp 2 x)
  have hflatten : Measurable flatten := by dsimp [flatten]; fun_prop
  have hconvert : Measurable convertFrame := by
    exact (measurable_standardComplexGaussianFrame_map m d).comp
      (MeasurableEquiv.toLp 2 _).measurable
  have hflat : ν.map flatten = μ := map_pi_rows (gaussianReal 0 1)
  have hcoord : convertFrame ∘ flatten =
      fun a : Fin m → (Fin d × Fin 2 → ℝ) ↦ fun i ↦ standardComplexTail (a i) := by
    funext a
    ext i j
    dsimp [convertFrame, flatten, realCoordinatesToComplexFrame, standardComplexTail]
    simp only [div_eq_mul_inv, Complex.ofReal_mul]
    ring
  have hbase : standardComplexGaussianFrame m d = μ.map convertFrame := by
    unfold standardComplexGaussianFrame
    rw [← map_pi_eq_stdGaussian]
    exact Measure.map_map
      (measurable_standardComplexGaussianFrame_map m d)
      (MeasurableEquiv.toLp 2 _).measurable
  rw [hbase, ← hflat, Measure.map_map hconvert hflatten, hcoord]
  exact Measure.pi_map_pi
    (fun _ ↦ measurable_standardComplexGaussianTail_map.aemeasurable)

/-- Two independent real standard Gaussians scaled to unit complex variance. -/
def scalarComplexMap (p : ℝ × ℝ) : ℂ :=
  ((p.1 / Real.sqrt 2 : ℝ) : ℂ) + ((p.2 / Real.sqrt 2 : ℝ) : ℂ) * Complex.I

/-- The standard circular complex Gaussian law. -/
def scalarComplexGaussian : Measure ℂ :=
  ((gaussianReal 0 1).prod (gaussianReal 0 1)).map scalarComplexMap

/-- The real-coordinate parametrisation of a complex Gaussian is continuous. -/
@[fun_prop]
theorem continuous_scalarComplexMap : Continuous scalarComplexMap := by
  unfold scalarComplexMap
  fun_prop

/-- The pushforward of the two independent real Gaussians is a probability measure. -/
instance : IsProbabilityMeasure scalarComplexGaussian :=
  Measure.isProbabilityMeasure_map continuous_scalarComplexMap.measurable.aemeasurable

/-- The vector law is the product of independent scalar complex Gaussian laws. -/
theorem standardComplexGaussianTail_eq_pi (n : ℕ) :
    standardComplexGaussianTail n = Measure.pi (fun _ : Fin n ↦ scalarComplexGaussian) := by
  have hscalar : (Measure.pi (fun _ : Fin 2 ↦ gaussianReal 0 1)).map
      (fun x : Fin 2 → ℝ ↦ scalarComplexMap (x 0, x 1)) = scalarComplexGaussian := by
    rw [scalarComplexGaussian,
      ← (measurePreserving_piFinTwo (fun _ : Fin 2 ↦ gaussianReal 0 1)).map_eq,
      Measure.map_map continuous_scalarComplexMap.measurable
        (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)).measurable]
    rfl
  unfold standardComplexGaussianTail
  rw [← map_pi_uncurry (I := Fin n) (J := Fin 2),
    Measure.map_map measurable_standardComplexGaussianTail_map (by fun_prop)]
  have he : standardComplexTail ∘ (fun a (p : Fin n × Fin 2) ↦ a p.1 p.2) =
      fun a : Fin n → Fin 2 → ℝ ↦ fun j ↦ scalarComplexMap (a j 0, a j 1) := rfl
  rw [he, Measure.pi_map_pi (f := fun _ : Fin n ↦ fun x : Fin 2 → ℝ ↦ scalarComplexMap (x 0, x 1))
    (fun _ ↦ by fun_prop)]
  simp_rw [hscalar]

/-- Two complex Gaussian coordinates have the product scalar law. -/
theorem standardComplexGaussianTail_map_pair :
    (standardComplexGaussianTail 2).map (fun z ↦ (z 0, z 1)) =
      scalarComplexGaussian.prod scalarComplexGaussian := by
  rw [standardComplexGaussianTail_eq_pi]
  exact (measurePreserving_piFinTwo (fun _ : Fin 2 ↦ scalarComplexGaussian)).map_eq

/-- The joint density of two independent standard real Gaussians in radial form. -/
theorem gaussian_real_pair_pdf (p : ℝ × ℝ) :
    gaussianPDFReal 0 1 p.1 * gaussianPDFReal 0 1 p.2 =
      (2 * Real.pi)⁻¹ * Real.exp (-((p.1 ^ 2 + p.2 ^ 2) / 2)) := by
  unfold gaussianPDFReal
  norm_num
  have hs : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have hexp : Real.exp (-p.1 ^ 2 / 2) * Real.exp (-p.2 ^ 2 / 2) =
      Real.exp (-((p.1 ^ 2 + p.2 ^ 2) / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc
    _ = (Real.sqrt (2 * Real.pi))⁻¹ ^ 2 *
        (Real.exp (-p.1 ^ 2 / 2) * Real.exp (-p.2 ^ 2 / 2)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    _ = _ := by rw [inv_pow, hs, hexp]; ring

/-- Complex conjugation preserves the scalar standard complex Gaussian law. -/
theorem scalarComplexGaussian_map_star :
    scalarComplexGaussian.map star = scalarComplexGaussian := by
  have hn : (gaussianReal 0 1).map (fun x : ℝ ↦ -x) = gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := 0) (v := 1))
  have hp :
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (fun p : ℝ × ℝ ↦ (p.1, -p.2)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
    have h := Measure.map_prod_map (gaussianReal 0 1) (gaussianReal 0 1)
      measurable_id measurable_neg
    change Measure.map (Prod.map id Neg.neg) _ = _
    simpa only [Measure.map_id, hn] using h.symm
  have he : (fun p : ℝ × ℝ ↦ star (scalarComplexMap p)) =
      scalarComplexMap ∘ (fun p : ℝ × ℝ ↦ (p.1, -p.2)) := by
    funext p
    simp [scalarComplexMap, neg_div]
  unfold scalarComplexGaussian
  rw [Measure.map_map (by fun_prop) (by unfold scalarComplexMap; fun_prop)]
  change Measure.map (fun p : ℝ × ℝ ↦ star (scalarComplexMap p)) _ = _
  rw [he, ← Measure.map_map (by unfold scalarComplexMap; fun_prop) (by fun_prop), hp]

/-- Coordinatewise conjugation preserves the vector standard complex Gaussian law. -/
theorem standardComplexGaussianTail_map_star (n : ℕ) :
    (standardComplexGaussianTail n).map star = standardComplexGaussianTail n := by
  rw [standardComplexGaussianTail_eq_pi]
  change (Measure.pi (fun _ : Fin n ↦ scalarComplexGaussian)).map
    (fun z j ↦ star (z j)) = Measure.pi (fun _ : Fin n ↦ scalarComplexGaussian)
  rw [Measure.pi_map_pi (f := fun _ : Fin n ↦ (star : ℂ → ℂ)) (fun _ ↦ by fun_prop)]
  simp only [scalarComplexGaussian_map_star]

/-- Split a vector into its first and second coordinate blocks. -/
def splitGaussianSum (m n : ℕ) (x : Signal (m + n)) : Signal m × Signal n :=
  (fun i ↦ x (finSumFinEquiv (Sum.inl i)), fun i ↦ x (finSumFinEquiv (Sum.inr i)))

/-- Coordinate-block splitting is continuous, including empty blocks. -/
@[fun_prop] theorem continuous_splitGaussianSum (m n : ℕ) :
    Continuous (splitGaussianSum m n) := by unfold splitGaussianSum; fun_prop

/-- Disjoint coordinate blocks of a complex Gaussian vector are independent. -/
theorem standardComplexGaussianTail_map_splitSum (m n : ℕ) :
    (standardComplexGaussianTail (m + n)).map (splitGaussianSum m n) =
      (standardComplexGaussianTail m).prod (standardComplexGaussianTail n) := by
  simp only [standardComplexGaussianTail_eq_pi]
  have h1 := measurePreserving_piCongrLeft
    (fun _ : Fin m ⊕ Fin n ↦ scalarComplexGaussian)
    ((finSumFinEquiv (m := m) (n := n)).symm : Fin (m+n) ≃ Fin m ⊕ Fin n)
  have h2 := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin m ⊕ Fin n ↦ scalarComplexGaussian)
  convert (h2.comp h1).map_eq using 1
  congr 1
  funext x
  ext i <;> simp [splitGaussianSum, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft, Equiv.piCongrLeft', MeasurableEquiv.sumPiEquivProdPi]

/-- Squared Euclidean energy is additive over the two coordinate blocks. -/
theorem signalEnergy_splitSum (m n : ℕ) (z : Signal (m + n)) :
    signalEnergy z = signalEnergy (splitGaussianSum m n z).1 +
      signalEnergy (splitGaussianSum m n z).2 := by
  unfold signalEnergy squaredEuclideanNorm splitGaussianSum
  rw [← Equiv.sum_comp (finSumFinEquiv (m := m) (n := n))]
  exact Fintype.sum_sum_type _

end NLA.FR05
