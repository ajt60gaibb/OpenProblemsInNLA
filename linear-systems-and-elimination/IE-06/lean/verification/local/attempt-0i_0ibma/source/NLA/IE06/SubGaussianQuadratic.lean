import Mathlib
import LeanCert.Tactic.Verification

/-! A conditional finite-dimensional quadratic tail from directional subGaussian
MGF bounds. This file does not assume or assert the Gaussian convex-restriction
theorem needed to establish those bounds in the IE-06 application. -/

set_option autoImplicit false
set_option leancert.trust "kernel"
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators
noncomputable section
namespace NLA.IE06.SubGaussianQuadratic

theorem gaussian_density_square_identity (z : ℝ) :
    gaussianPDFReal 0 2 z * exp (z ^ 2 / 8) =
      sqrt 2 * gaussianPDFReal 0 4 z := by
  have hp : 0 < 4 * π := by positivity
  have hs : sqrt (8 * π) = sqrt 2 * sqrt (4 * π) := by
    rw [show 8 * π = 2 * (4 * π) by ring, sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  simp only [gaussianPDFReal_def, NNReal.coe_ofNat, sub_zero]
  rw [show 2 * π * 2 = 4 * π by ring, show 2 * π * 4 = 8 * π by ring]
  rw [mul_assoc, ← exp_add, hs]
  have he : -(z ^ 2) / (2 * 2) + z ^ 2 / 8 = -(z ^ 2) / (2 * 4) := by ring
  rw [he]
  have hs2 : (sqrt (2:ℝ)) ^ 2 = 2 := sq_sqrt (by norm_num)
  have hs0 : sqrt (4 * π) ≠ 0 := (sqrt_pos.2 hp).ne'
  have hstwo : sqrt (2:ℝ) ≠ 0 := (sqrt_pos.2 (by norm_num)).ne'
  field_simp

theorem gaussian_exp_square_integrable :
    Integrable (fun z : ℝ => exp (z ^ 2 / 8)) (gaussianReal 0 2) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (2:NNReal) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 2) (ae_of_all _ (fun z => gaussianPDF_lt_top))]
  simpa only [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
    smul_eq_mul, gaussian_density_square_identity] using
    (integrable_gaussianPDFReal 0 4).const_mul (sqrt 2)

theorem gaussian_exp_square_integral :
    (∫ z : ℝ, exp (z ^ 2 / 8) ∂gaussianReal 0 2) = sqrt 2 := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (2:NNReal) ≠ 0)]
  simp only [smul_eq_mul, gaussian_density_square_identity, integral_const_mul]
  rw [integral_gaussianPDFReal_eq_one 0 (by norm_num : (4:NNReal) ≠ 0), mul_one]

theorem scalar_exp_square {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    (h : HasSubgaussianMGF Y 1 μ) :
    Integrable (fun ω => exp (Y ω ^ 2 / 4)) μ ∧
      (∫ ω, exp (Y ω ^ 2 / 4) ∂μ) ≤ sqrt 2 := by
  let f : ℝ × Ω → ℝ := fun p => exp ((p.1 / 2) * Y p.2)
  have hfm : StronglyMeasurable f := by
    apply Measurable.stronglyMeasurable
    dsimp [f]
    fun_prop
  have hb (z : ℝ) : (∫ ω, f (z, ω) ∂μ) ≤ exp (z ^ 2 / 8) := by
    have hm := h.mgf_le (z / 2)
    simpa only [mgf, NNReal.coe_one, one_mul,
      show (z / 2)^2 / 2 = z^2 / 8 by ring] using hm
  have hfnorm (z : ℝ) : (∫ ω, ‖f (z, ω)‖ ∂μ) = ∫ ω, f (z, ω) ∂μ := by
    apply integral_congr_ae
    exact ae_of_all _ (fun ω => Real.norm_of_nonneg (exp_pos _).le)
  have hinner : Integrable (fun z => ∫ ω, f (z, ω) ∂μ) (gaussianReal 0 2) := by
    apply gaussian_exp_square_integrable.mono' hfm.integral_prod_right.aestronglyMeasurable
    apply ae_of_all
    intro z
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => (exp_pos _).le))]
    exact hb z
  have hf : Integrable f ((gaussianReal 0 2).prod μ) := by
    apply (integrable_prod_iff hfm.aestronglyMeasurable).2
    constructor
    · exact ae_of_all _ (fun z => h.integrable_exp_mul (z / 2))
    · simpa only [hfnorm] using hinner
  have hid (ω : Ω) : (∫ z, f (z, ω) ∂gaussianReal 0 2) = exp (Y ω ^ 2 / 4) := by
    have hg := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 2)) (Y ω / 2)
    simp only [mgf, zero_mul, zero_add, NNReal.coe_ofNat] at hg
    have he : 2 * (Y ω / 2)^2 / 2 = Y ω ^ 2 / 4 := by ring
    rw [he] at hg
    calc
      (∫ z, f (z, ω) ∂gaussianReal 0 2) =
          ∫ z, exp ((Y ω / 2) * z) ∂gaussianReal 0 2 := by
        apply integral_congr_ae
        apply ae_of_all
        intro z
        dsimp [f]
        congr 1
        ring
      _ = _ := hg
  constructor
  · simpa only [hid] using hf.integral_prod_right
  · rw [← gaussian_exp_square_integral]
    calc
      (∫ ω, exp (Y ω ^ 2 / 4) ∂μ) =
          ∫ z, ∫ ω, f (z, ω) ∂μ ∂gaussianReal 0 2 := by
            rw [integral_integral_swap hf]
            simp only [hid]
      _ ≤ _ := integral_mono hinner gaussian_exp_square_integrable hb



def columnSq {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) (j : Fin b) : ℝ :=
  ∑ i, M i j ^ 2

def frobeniusSq {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) : ℝ :=
  ∑ j, columnSq M j

def projection {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ)
    (v : Fin a → ℝ) (j : Fin b) : ℝ := ∑ i, M i j * v i

def quadratic {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) (v : Fin a → ℝ) : ℝ :=
  ∑ j, projection M v j ^ 2

def DirectionalSubGaussian {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {a : ℕ} (X : Ω → Fin a → ℝ) : Prop :=
  ∀ v : Fin a → ℝ, HasSubgaussianMGF (fun ω => ∑ i, v i * X ω i)
    ⟨∑ i, v i ^ 2, Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩ μ

theorem columnSq_nonneg {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) (j : Fin b) :
    0 ≤ columnSq M j := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem frobeniusSq_nonneg {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) :
    0 ≤ frobeniusSq M := Finset.sum_nonneg (fun j _ => columnSq_nonneg M j)

theorem column_eq_zero_of_columnSq_zero {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ)
    (j : Fin b) (h : columnSq M j = 0) (i : Fin a) : M i j = 0 := by
  have hi : M i j ^ 2 ≤ columnSq M j :=
    Finset.single_le_sum (fun k _ => sq_nonneg (M k j)) (Finset.mem_univ i)
  rw [h] at hi
  nlinarith [sq_nonneg (M i j)]

theorem normalized_sum_squares_le {a : ℕ} (v : Fin a → ℝ) :
    (∑ i, (v i / sqrt (∑ k, v k ^ 2)) ^ 2) ≤ 1 := by
  have hs : 0 ≤ ∑ k, v k ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  simp_rw [div_pow]
  rw [sq_sqrt hs, ← Finset.sum_div]
  by_cases hz : ∑ k, v k ^ 2 = 0
  · simp [hz]
  · rw [div_self hz]

theorem normalized_projection_subGaussian {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {a b : ℕ} {X : Ω → Fin a → ℝ}
    (hX : DirectionalSubGaussian μ X) (M : Matrix (Fin a) (Fin b) ℝ) (j : Fin b) :
    HasSubgaussianMGF
      (fun ω => projection M (X ω) j / sqrt (columnSq M j)) 1 μ := by
  have h := hX (fun i => M i j / sqrt (columnSq M j))
  have he : (fun ω => ∑ i, (M i j / sqrt (columnSq M j)) * X ω i) =
      (fun ω => projection M (X ω) j / sqrt (columnSq M j)) := by
    funext ω
    simp only [projection, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at h
  refine ⟨h.integrable_exp_mul, fun t => (h.mgf_le t).trans ?_⟩
  apply exp_le_exp.mpr
  change (∑ i, (M i j / sqrt (columnSq M j)) ^ 2) * t ^ 2 / 2 ≤ 1 * t ^ 2 / 2
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (normalized_sum_squares_le (fun i => M i j))
      (sq_nonneg t)) (by norm_num)

theorem weighted_normalized_square {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ)
    (v : Fin a → ℝ) (j : Fin b) :
    (columnSq M j / frobeniusSq M) *
        ((projection M v j / sqrt (columnSq M j)) ^ 2 / 4) =
      (projection M v j) ^ 2 / (4 * frobeniusSq M) := by
  have hs := columnSq_nonneg M j
  by_cases hz : columnSq M j = 0
  · have hp : projection M v j = 0 := by
      simp [projection, column_eq_zero_of_columnSq_zero M j hz]
    simp [hz, hp]
  · rw [div_pow, sq_sqrt hs]
    field_simp

theorem frobenius_exp_square {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a b : ℕ} {X : Ω → Fin a → ℝ} (hXm : Measurable X)
    (hX : DirectionalSubGaussian μ X) (M : Matrix (Fin a) (Fin b) ℝ)
    (hF : 0 < frobeniusSq M) :
    Integrable (fun ω => exp (quadratic M (X ω) / (4 * frobeniusSq M))) μ ∧
      (∫ ω, exp (quadratic M (X ω) / (4 * frobeniusSq M)) ∂μ) ≤ sqrt 2 := by
  let w : Fin b → ℝ := fun j => columnSq M j / frobeniusSq M
  let Y : Fin b → Ω → ℝ := fun j ω => projection M (X ω) j / sqrt (columnSq M j)
  have hw (j : Fin b) : 0 ≤ w j := div_nonneg (columnSq_nonneg M j) hF.le
  have hw1 : ∑ j, w j = 1 := by
    dsimp [w]
    rw [← Finset.sum_div]
    exact div_self hF.ne'
  have hYm (j : Fin b) : Measurable (Y j) := by
    dsimp [Y, projection]
    fun_prop
  have hY (j : Fin b) : Integrable (fun ω => exp (Y j ω ^ 2 / 4)) μ ∧
      (∫ ω, exp (Y j ω ^ 2 / 4) ∂μ) ≤ sqrt 2 :=
    scalar_exp_square (hYm j) (normalized_projection_subGaussian hX M j)
  have hid (ω : Ω) : (∑ j, w j * (Y j ω ^ 2 / 4)) =
      quadratic M (X ω) / (4 * frobeniusSq M) := by
    simp only [w, Y, weighted_normalized_square, quadratic, Finset.sum_div]
  have hjensen (ω : Ω) :
      exp (quadratic M (X ω) / (4 * frobeniusSq M)) ≤
        ∑ j, w j * exp (Y j ω ^ 2 / 4) := by
    rw [← hid ω]
    exact convexOn_exp.map_sum_le (fun j _ => hw j) hw1 (fun _ _ => Set.mem_univ _)
  have hsum : Integrable (fun ω => ∑ j, w j * exp (Y j ω ^ 2 / 4)) μ :=
    integrable_finsetSum _ (fun j _ => (hY j).1.const_mul (w j))
  have hi : Integrable (fun ω => exp (quadratic M (X ω) / (4 * frobeniusSq M))) μ := by
    apply hsum.mono'
    · apply Measurable.aestronglyMeasurable
      dsimp [quadratic, projection]
      fun_prop
    · exact ae_of_all _ (fun ω => by
        rw [Real.norm_of_nonneg (exp_pos _).le]
        exact hjensen ω)
  refine ⟨hi, (integral_mono hi hsum hjensen).trans ?_⟩
  rw [integral_finsetSum _ (fun j _ => (hY j).1.const_mul (w j))]
  simp only [integral_const_mul]
  calc
    (∑ j, w j * ∫ ω, exp (Y j ω ^ 2 / 4) ∂μ) ≤ ∑ j, w j * sqrt 2 :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hY j).2 (hw j))
    _ = sqrt 2 := by rw [← Finset.sum_mul, hw1, one_mul]



theorem sqrt_two_le_exp_half : sqrt 2 ≤ exp (1 / 2 : ℝ) := by
  have he : exp (1 / 2 : ℝ) ^ 2 = exp 1 := by
    rw [pow_two, ← exp_add]
    norm_num
  have h2 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1:ℝ)]
  have hs : sqrt (2:ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  nlinarith [sqrt_nonneg (2:ℝ), exp_pos (1 / 2 : ℝ)]

theorem quadratic_zero_of_frobeniusSq_zero {a b : ℕ}
    (M : Matrix (Fin a) (Fin b) ℝ) (hF : frobeniusSq M = 0) (v : Fin a → ℝ) :
    quadratic M v = 0 := by
  have hs (j : Fin b) : columnSq M j = 0 := by
    have hj : columnSq M j ≤ frobeniusSq M :=
      Finset.single_le_sum (fun k _ => columnSq_nonneg M k) (Finset.mem_univ j)
    linarith [columnSq_nonneg M j]
  simp [quadratic, projection, column_eq_zero_of_columnSq_zero M _ (hs _)]

theorem quadratic_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a b : ℕ} {X : Ω → Fin a → ℝ} (hXm : Measurable X)
    (hX : DirectionalSubGaussian μ X) (M : Matrix (Fin a) (Fin b) ℝ)
    (x : ℝ) (_hx : 0 ≤ x) :
    μ {ω | (2 + 4 * x) * frobeniusSq M < quadratic M (X ω)} ≤
      ENNReal.ofReal (exp (-x)) := by
  by_cases hF : frobeniusSq M = 0
  · simp [hF, quadratic_zero_of_frobeniusSq_zero M hF]
  have hFp : 0 < frobeniusSq M := lt_of_le_of_ne (frobeniusSq_nonneg M) (Ne.symm hF)
  obtain ⟨hi, hb⟩ := frobenius_exp_square hXm hX M hFp
  let f : Ω → ℝ := fun ω =>
    exp (-(1 / 2 + x)) * exp (quadratic M (X ω) / (4 * frobeniusSq M))
  have hfi : Integrable f μ := hi.const_mul _
  have hfn : 0 ≤ᵐ[μ] f := ae_of_all _ (fun _ => by dsimp [f]; positivity)
  have hmarkov := hfi.measure_le_integral hfn
    (s := {ω | (2 + 4 * x) * frobeniusSq M < quadratic M (X ω)}) (by
      intro ω hω
      dsimp [f]
      rw [← exp_add]
      apply one_le_exp_iff.mpr
      have hdiv : 1 / 2 + x < quadratic M (X ω) / (4 * frobeniusSq M) := by
        apply (lt_div_iff₀ (by positivity : 0 < 4 * frobeniusSq M)).2
        dsimp at hω
        nlinarith
      linarith)
  apply hmarkov.trans
  apply ENNReal.ofReal_le_ofReal
  change (∫ ω, exp (-(1 / 2 + x)) *
    exp (quadratic M (X ω) / (4 * frobeniusSq M)) ∂μ) ≤ exp (-x)
  rw [integral_const_mul]
  calc
    exp (-(1 / 2 + x)) * (∫ ω, exp (quadratic M (X ω) / (4 * frobeniusSq M)) ∂μ)
        ≤ exp (-(1 / 2 + x)) * exp (1 / 2) :=
      mul_le_mul_of_nonneg_left (hb.trans sqrt_two_le_exp_half) (exp_pos _).le
    _ = exp (-x) := by rw [← exp_add]; congr 1; ring

#assert_trust kernel gaussian_density_square_identity
#assert_trust kernel gaussian_exp_square_integrable
#assert_trust kernel gaussian_exp_square_integral
#assert_trust kernel scalar_exp_square
#assert_trust kernel columnSq
#assert_trust kernel frobeniusSq
#assert_trust kernel projection
#assert_trust kernel quadratic
#assert_trust kernel DirectionalSubGaussian
#assert_trust kernel columnSq_nonneg
#assert_trust kernel frobeniusSq_nonneg
#assert_trust kernel column_eq_zero_of_columnSq_zero
#assert_trust kernel normalized_sum_squares_le
#assert_trust kernel normalized_projection_subGaussian
#assert_trust kernel weighted_normalized_square
#assert_trust kernel frobenius_exp_square
#assert_trust kernel sqrt_two_le_exp_half
#assert_trust kernel quadratic_zero_of_frobeniusSq_zero
#assert_trust kernel quadratic_tail

#print axioms gaussian_density_square_identity
#print axioms gaussian_exp_square_integrable
#print axioms gaussian_exp_square_integral
#print axioms scalar_exp_square
#print axioms columnSq
#print axioms frobeniusSq
#print axioms projection
#print axioms quadratic
#print axioms DirectionalSubGaussian
#print axioms columnSq_nonneg
#print axioms frobeniusSq_nonneg
#print axioms column_eq_zero_of_columnSq_zero
#print axioms normalized_sum_squares_le
#print axioms normalized_projection_subGaussian
#print axioms weighted_normalized_square
#print axioms frobenius_exp_square
#print axioms sqrt_two_le_exp_half
#print axioms quadratic_zero_of_frobeniusSq_zero
#print axioms quadratic_tail

end NLA.IE06.SubGaussianQuadratic
