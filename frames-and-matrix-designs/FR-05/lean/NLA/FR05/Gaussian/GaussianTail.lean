/-
The complex-Gaussian part of the planted norm estimate (3.22).

The source uses Euclidean norms, whereas a finite function type has Lean's
sup norm by default.  We therefore retain the explicit energy sum from
`Planted.lean` throughout this module.
-/
import NLA.FR05.Geometry.Planted
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.NormNum.RealSqrt

set_option autoImplicit false
open scoped BigOperators ComplexConjugate Matrix Topology
noncomputable section

namespace NLA.FR05

open MeasureTheory ProbabilityTheory

/-- Source-style notation for the explicit squared Euclidean energy. -/
abbrev signalEnergy {n : ℕ} (x : Signal n) : ℝ :=
  squaredEuclideanNorm x

theorem signalEnergy_joinTwo {n : ℕ} (u v : ℂ) (w : Signal n) :
    signalEnergy (joinTwo u v w) =
      Complex.normSq u + Complex.normSq v + signalEnergy w := by
  exact squaredEuclideanNorm_joinTwo u v w

theorem signalEnergy_plantedColumn {n : ℕ} (r : PlantedRow n) :
    signalEnergy (plantedColumn r) = r.radial + signalEnergy r.tail := by
  exact squaredEuclideanNorm_plantedColumn r

theorem mgf_square_standardGaussian_quarter :
    mgf (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) (1 / 4) = Real.sqrt 2 := by
  unfold mgf
  rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num)]
  simp only [smul_eq_mul]
  unfold gaussianPDFReal
  norm_num
  have h_integrand : ∀ x : ℝ,
      (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ * Real.exp (-x ^ 2 / 2) *
          Real.exp (1 / 4 * x ^ 2) =
        ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹) *
          Real.exp (-(1 / 4) * x ^ 2) := by
    intro x
    calc
      (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ * Real.exp (-x ^ 2 / 2) *
          Real.exp (1 / 4 * x ^ 2) =
        ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹) *
          (Real.exp (-x ^ 2 / 2) * Real.exp (1 / 4 * x ^ 2)) := by ring
      _ = ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹) *
          Real.exp (-(1 / 4) * x ^ 2) := by
        rw [← Real.exp_add]
        congr 2
        ring
  simp_rw [h_integrand]
  rw [integral_const_mul, integral_gaussian]
  rw [Real.sqrt_div Real.pi_pos.le]
  norm_num
  field_simp [Real.sqrt_ne_zero'.mpr Real.pi_pos]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem integrable_exp_quarter_square_standardGaussian :
    Integrable (fun x : ℝ ↦ Real.exp ((1 / 4) * x ^ 2))
      (gaussianReal 0 1) := by
  rw [← mgf_pos_iff]
  rw [mgf_square_standardGaussian_quarter]
  positivity

theorem mgf_sum_square_product_quarter
    {ι : Type*} [Fintype ι] :
    mgf (fun x : ι → ℝ ↦ ∑ i, x i ^ 2)
      (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) (1 / 4) =
      (Real.sqrt 2) ^ Fintype.card ι := by
  unfold mgf
  have hrewrite :
      (fun x : ι → ℝ ↦ Real.exp ((1 / 4) * ∑ i, x i ^ 2)) =
        fun x ↦ ∏ i, Real.exp ((1 / 4) * x i ^ 2) := by
    funext x
    rw [Finset.mul_sum]
    rw [Real.exp_sum]
  rw [hrewrite,
    integral_fintype_prod_eq_prod (f := fun _ x ↦ Real.exp ((1 / 4) * x ^ 2))]
  have hsingle : ∫ x : ℝ, Real.exp ((1 / 4) * x ^ 2) ∂gaussianReal 0 1 =
      Real.sqrt 2 := by
    exact mgf_square_standardGaussian_quarter
  simp_rw [hsingle]
  simp

theorem tail_sum_square_product_quarter
    {ι : Type*} [Fintype ι] (R : ℝ) :
    (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)).real
        {x | R ≤ ∑ i, x i ^ 2} ≤
      Real.exp (-(1 / 4) * R) * (Real.sqrt 2) ^ Fintype.card ι := by
  let μ : Measure (ι → ℝ) :=
    Measure.pi (fun _ : ι ↦ gaussianReal 0 1)
  let X : (ι → ℝ) → ℝ := fun x ↦ ∑ i, x i ^ 2
  have hmgf : mgf X μ (1 / 4) = (Real.sqrt 2) ^ Fintype.card ι := by
    simpa [X, μ] using (mgf_sum_square_product_quarter (ι := ι))
  have hpositive : 0 < mgf X μ (1 / 4) := by
    rw [hmgf]
    positivity
  have hint : Integrable (fun x ↦ Real.exp ((1 / 4) * X x)) μ :=
    mgf_pos_iff.mp hpositive
  calc
    μ.real {x | R ≤ X x} ≤ Real.exp (-(1 / 4) * R) * mgf X μ (1 / 4) :=
      measure_ge_le_exp_mul_mgf R (by norm_num) hint
    _ = Real.exp (-(1 / 4) * R) * (Real.sqrt 2) ^ Fintype.card ι := by
      rw [hmgf]

/-- A standard complex Gaussian tail represented by two independent real
standard-Gaussian coordinates and scaled to variance one half per component. -/
def standardComplexTail {n : ℕ} (x : (Fin n × Fin 2) → ℝ) : Signal n :=
  fun j ↦ ((x (j, 0) / Real.sqrt 2 : ℝ) : ℂ) +
    ((x (j, 1) / Real.sqrt 2 : ℝ) : ℂ) * Complex.I

/-- One standard complex-Gaussian tail row in `ℂⁿ`, using exactly the
real-coordinate representation used for the tail estimates below. -/
def standardComplexGaussianTail (n : ℕ) : Measure (Signal n) :=
  (Measure.pi (fun _ : Fin n × Fin 2 ↦ gaussianReal 0 1)).map standardComplexTail

@[fun_prop]
theorem measurable_standardComplexGaussianTail_map {n : ℕ} :
    Measurable (standardComplexTail (n := n)) := by
  unfold standardComplexTail
  fun_prop

instance isProbabilityMeasure_standardComplexGaussianTail (n : ℕ) :
    IsProbabilityMeasure (standardComplexGaussianTail n) := by
  let : IsProbabilityMeasure
      (Measure.pi (fun _ : Fin n × Fin 2 ↦ gaussianReal 0 1)) :=
    @MeasureTheory.Measure.pi.instIsProbabilityMeasure
      (Fin n × Fin 2) (fun _ ↦ ℝ) _ _
      (fun _ ↦ gaussianReal 0 1) (fun _ ↦ inferInstance)
  exact Measure.isProbabilityMeasure_map
    (measurable_standardComplexGaussianTail_map (n := n)).aemeasurable

theorem signalEnergy_standardComplexTail {n : ℕ} (x : (Fin n × Fin 2) → ℝ) :
    signalEnergy (standardComplexTail x) =
      (1 / 2 : ℝ) * ∑ j, x j ^ 2 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
  have hcoord (j : Fin n) :
      Complex.normSq (standardComplexTail x j) =
        (1 / 2 : ℝ) * (x (j, 0) ^ 2 + x (j, 1) ^ 2) := by
    rw [standardComplexTail, Complex.normSq_add_mul_I]
    field_simp
    nlinarith
  unfold signalEnergy squaredEuclideanNorm
  simp_rw [hcoord]
  rw [← Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  simp_rw [Fin.sum_univ_two]

theorem tail_standardComplexTail (n : ℕ) (R : ℝ) :
    (Measure.pi (fun _ : Fin n × Fin 2 ↦ gaussianReal 0 1)).real
        {x | R ≤ signalEnergy (standardComplexTail x)} ≤
      Real.exp (-(1 / 4) * (2 * R)) * (Real.sqrt 2) ^ (n * 2) := by
  let μ : Measure ((Fin n × Fin 2) → ℝ) :=
    Measure.pi (fun _ : Fin n × Fin 2 ↦ gaussianReal 0 1)
  let E : ((Fin n × Fin 2) → ℝ) → ℝ :=
    fun x ↦ signalEnergy (standardComplexTail x)
  let X : ((Fin n × Fin 2) → ℝ) → ℝ := fun x ↦ ∑ i, x i ^ 2
  have henergy : ∀ x, E x = (1 / 2 : ℝ) * X x := by
    intro x
    exact signalEnergy_standardComplexTail x
  have hsubset : {x | R ≤ E x} ⊆ {x | 2 * R ≤ X x} := by
    intro x hx
    change R ≤ E x at hx
    change 2 * R ≤ X x
    rw [henergy x] at hx
    linarith
  calc
    μ.real {x | R ≤ E x} ≤ μ.real {x | 2 * R ≤ X x} :=
      measureReal_mono hsubset
    _ ≤ Real.exp (-(1 / 4) * (2 * R)) * (Real.sqrt 2) ^
          Fintype.card (Fin n × Fin 2) :=
      tail_sum_square_product_quarter (ι := Fin n × Fin 2) (2 * R)
    _ = Real.exp (-(1 / 4) * (2 * R)) * (Real.sqrt 2) ^ (n * 2) := by
      norm_num [Fintype.card_prod]

/-- The source-scale complex Gaussian tail used in (3.22). -/
theorem tail_standardComplexTail_eight_mul (n : ℕ) :
    (Measure.pi (fun _ : Fin n × Fin 2 ↦ gaussianReal 0 1)).real
        {x | 8 * (n : ℝ) ≤ signalEnergy (standardComplexTail x)} ≤
      Real.exp (-3 * (n : ℝ)) := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    nlinarith [Real.add_one_le_exp 1]
  have hpow : (2 : ℝ) ^ n ≤ (Real.exp 1) ^ n :=
    pow_le_pow_left₀ (by norm_num) htwo n
  have hpow' : (2 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
    simpa [Real.exp_nat_mul] using hpow
  calc
    (Measure.pi (fun _ : Fin n × Fin 2 ↦ gaussianReal 0 1)).real
        {x | 8 * (n : ℝ) ≤ signalEnergy (standardComplexTail x)} ≤
      Real.exp (-(1 / 4) * (2 * (8 * (n : ℝ)))) *
        (Real.sqrt 2) ^ (n * 2) :=
      tail_standardComplexTail n (8 * (n : ℝ))
    _ = Real.exp (-4 * (n : ℝ)) * (2 : ℝ) ^ n := by
      rw [show n * 2 = 2 * n by lia, pow_mul, hsqrt]
      congr 2
      ring
    _ ≤ Real.exp (-4 * (n : ℝ)) * Real.exp (n : ℝ) := by
      gcongr
    _ = Real.exp (-3 * (n : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- A finite-row union bound.  Combining a radial and a complex-Gaussian
tail at threshold `8M` gives the `16M` row-energy threshold used in (3.22). -/
theorem row_energy_max_tail_of_component_tails
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : ℕ) (M a b : ℝ)
    (radial tail : Fin m → Ω → ℝ)
    (hradial : ∀ i, μ.real {ω | 8 * M ≤ radial i ω} ≤ a)
    (htail : ∀ i, μ.real {ω | 8 * M ≤ tail i ω} ≤ b) :
    μ.real {ω | ∃ i, 16 * M ≤ radial i ω + tail i ω} ≤ m * (a + b) := by
  have hrow (i : Fin m) :
      μ.real {ω | 16 * M ≤ radial i ω + tail i ω} ≤ a + b := by
    have hsubset : {ω | 16 * M ≤ radial i ω + tail i ω} ⊆
        {ω | 8 * M ≤ radial i ω} ∪ {ω | 8 * M ≤ tail i ω} := by
      intro ω hω
      by_cases hr : 8 * M ≤ radial i ω
      · exact Or.inl hr
      · right
        by_contra ht
        change 16 * M ≤ radial i ω + tail i ω at hω
        change ¬ 8 * M ≤ tail i ω at ht
        have hr' : radial i ω < 8 * M := lt_of_not_ge hr
        have ht' : tail i ω < 8 * M := lt_of_not_ge ht
        linarith
    calc
      μ.real {ω | 16 * M ≤ radial i ω + tail i ω} ≤
          μ.real ({ω | 8 * M ≤ radial i ω} ∪ {ω | 8 * M ≤ tail i ω}) :=
        measureReal_mono hsubset
      _ ≤ μ.real {ω | 8 * M ≤ radial i ω} + μ.real {ω | 8 * M ≤ tail i ω} :=
        measureReal_union_le _ _
      _ ≤ a + b := add_le_add (hradial i) (htail i)
  have hsubset : {ω | ∃ i, 16 * M ≤ radial i ω + tail i ω} ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin m)),
        {ω | 16 * M ≤ radial i ω + tail i ω} := by
    intro ω hω
    obtain ⟨i, hi⟩ := hω
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨Finset.mem_univ i, hi⟩⟩
  calc
    μ.real {ω | ∃ i, 16 * M ≤ radial i ω + tail i ω} ≤
        μ.real (⋃ i ∈ (Finset.univ : Finset (Fin m)),
          {ω | 16 * M ≤ radial i ω + tail i ω}) :=
      measureReal_mono hsubset (measure_lt_top μ _).ne
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin m)),
        μ.real {ω | 16 * M ≤ radial i ω + tail i ω} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin m)), (a + b) := by
      gcongr with i hi
      exact hrow i
    _ = m * (a + b) := by
      simp [nsmul_eq_mul]
      ring

end NLA.FR05
