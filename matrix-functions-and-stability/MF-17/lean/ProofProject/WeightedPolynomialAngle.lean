import ProofProject.PolynomialGeometryReduction
import ProofProject.ProjectionAngle
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! The exact analytic/strictly-negative angle bound for finite weighted Laurent polynomials. -/

noncomputable section

open MeasureTheory

namespace ProofProject

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

lemma laurentCirclePolynomial_add (a b : ℤ →₀ ℂ) (z : AddCircle (1 : ℝ)) :
    laurentCirclePolynomial (a + b) z =
      laurentCirclePolynomial a z + laurentCirclePolynomial b z := by
  change (a + b).sum (fun m c => c * fourier m z) =
    a.sum (fun m c => c * fourier m z) + b.sum (fun m c => c * fourier m z)
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

lemma laurentCirclePolynomial_smul (t : ℂ) (a : ℤ →₀ ℂ) (z : AddCircle (1 : ℝ)) :
    laurentCirclePolynomial (t • a) z = t * laurentCirclePolynomial a z := by
  change (t • a).sum (fun m c => c * fourier m z) =
    t * a.sum (fun m c => c * fourier m z)
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
  simp only [Finsupp.sum, Finset.mul_sum, mul_assoc]

/-- Squared norm for the polynomial circle weight, with normalized Haar measure. -/
def polynomialCircleEnergy (p : Polynomial ℂ) (c : ℤ →₀ ℂ) : ℝ :=
  ∫ z : AddCircle (1 : ℝ), ‖laurentCirclePolynomial c z‖ ^ 2 *
    ‖p.eval (fourier 1 z)‖ ^ 2 ∂AddCircle.haarAddCircle

/-- The complex weighted pairing, conjugate-linear in its first argument. -/
def polynomialCirclePairing (p : Polynomial ℂ) (a b : ℤ →₀ ℂ) : ℂ :=
  ∫ z : AddCircle (1 : ℝ), starRingEnd ℂ (laurentCirclePolynomial a z) *
    laurentCirclePolynomial b z * ((‖p.eval (fourier 1 z)‖ ^ 2 : ℝ) : ℂ)
      ∂AddCircle.haarAddCircle

lemma polynomialCircleEnergy_nonneg (p : Polynomial ℂ) (c : ℤ →₀ ℂ) :
    0 ≤ polynomialCircleEnergy p c :=
  integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

def weightedLaurentFunction (p : Polynomial ℂ) (c : ℤ →₀ ℂ)
    (z : AddCircle (1 : ℝ)) : ℂ :=
  laurentCirclePolynomial c z * p.eval (fourier 1 z)

lemma continuous_weightedLaurentFunction (p : Polynomial ℂ) (c : ℤ →₀ ℂ) :
    Continuous (weightedLaurentFunction p c) :=
  (continuous_laurentCirclePolynomial c).mul
    (p.continuous.comp (fourier (T := (1 : ℝ)) 1).continuous)

lemma weightedLaurentFunction_memLp (p : Polynomial ℂ) (c : ℤ →₀ ℂ) :
    MemLp (weightedLaurentFunction p c) 2 AddCircle.haarAddCircle :=
  (continuous_weightedLaurentFunction p c).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma polynomialCircleEnergy_integrable (p : Polynomial ℂ) (c : ℤ →₀ ℂ) :
    Integrable (fun z : AddCircle (1 : ℝ) => ‖laurentCirclePolynomial c z‖ ^ 2 *
      ‖p.eval (fourier 1 z)‖ ^ 2) AddCircle.haarAddCircle := by
  simpa only [weightedLaurentFunction, norm_mul, mul_pow] using
    (weightedLaurentFunction_memLp p c).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)

abbrev PolynomialCircleL2 := Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))

def weightedLaurentL2 (p : Polynomial ℂ) (c : ℤ →₀ ℂ) : PolynomialCircleL2 :=
  (weightedLaurentFunction_memLp p c).toLp (weightedLaurentFunction p c)

lemma weightedLaurentL2_coe (p : Polynomial ℂ) (c : ℤ →₀ ℂ) :
    (weightedLaurentL2 p c : AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      weightedLaurentFunction p c :=
  (weightedLaurentFunction_memLp p c).coeFn_toLp

/-- The continuous-map and `MemLp` realizations give the same L² vector. -/
lemma weightedLaurentL2_eq_continuousToLp (p : Polynomial ℂ) (c : ℤ →₀ ℂ) :
    weightedLaurentL2 p c = ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
      ⟨weightedLaurentFunction p c, continuous_weightedLaurentFunction p c⟩ := by
  apply Lp.ext
  exact (weightedLaurentL2_coe p c).trans
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
      ⟨weightedLaurentFunction p c, continuous_weightedLaurentFunction p c⟩).symm

/-- Exact norm identity for continuous functions mapped to normalized circle L². -/
lemma circleContinuous_toLp_norm_sq (f : C(AddCircle (1 : ℝ), ℂ)) :
    ‖ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ f‖ ^ 2 =
      ∫ z : AddCircle (1 : ℝ), ‖f z‖ ^ 2 ∂AddCircle.haarAddCircle := by
  let v : PolynomialCircleL2 := ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ f
  change ‖v‖ ^ 2 = _
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) v v)]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
    AddCircle.haarAddCircle f] with z hz
  change v z = f z at hz
  rw [hz, inner_self_eq_norm_sq]

lemma weightedLaurentL2_add_smul (p : Polynomial ℂ) (a b : ℤ →₀ ℂ) (t : ℂ) :
    weightedLaurentL2 p (a + t • b) = weightedLaurentL2 p a + t • weightedLaurentL2 p b := by
  apply Lp.ext
  filter_upwards [weightedLaurentL2_coe p (a + t • b), weightedLaurentL2_coe p a,
    weightedLaurentL2_coe p b, Lp.coeFn_add (weightedLaurentL2 p a) (t • weightedLaurentL2 p b),
    Lp.coeFn_smul t (weightedLaurentL2 p b)] with z hab ha hb hadd hsmul
  simp only [Pi.add_apply] at hadd
  simp only [Pi.smul_apply] at hsmul
  rw [hab, hadd, ha, hsmul, hb]
  simp only [weightedLaurentFunction, laurentCirclePolynomial_add,
    laurentCirclePolynomial_smul, Pi.smul_apply, smul_eq_mul]
  ring

lemma weightedLaurentL2_norm_sq (p : Polynomial ℂ) (c : ℤ →₀ ℂ) :
    ‖weightedLaurentL2 p c‖ ^ 2 = polynomialCircleEnergy p c := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) (weightedLaurentL2 p c) (weightedLaurentL2 p c))]
  apply integral_congr_ae
  filter_upwards [weightedLaurentL2_coe p c] with z hz
  rw [hz, inner_self_eq_norm_sq]
  simp only [weightedLaurentFunction, norm_mul, mul_pow]

lemma weightedLaurentL2_norm (p : Polynomial ℂ) (c : ℤ →₀ ℂ) :
    ‖weightedLaurentL2 p c‖ = Real.sqrt (polynomialCircleEnergy p c) := by
  rw [← weightedLaurentL2_norm_sq, Real.sqrt_sq (norm_nonneg _)]

lemma weightedLaurentL2_inner (p : Polynomial ℂ) (a b : ℤ →₀ ℂ) :
    inner ℂ (weightedLaurentL2 p a) (weightedLaurentL2 p b) =
      polynomialCirclePairing p a b := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weightedLaurentL2_coe p a, weightedLaurentL2_coe p b] with z ha hb
  rw [RCLike.inner_apply', ha, hb]
  simp only [weightedLaurentFunction, map_mul]
  have hnorm : starRingEnd ℂ (p.eval (fourier 1 z)) * p.eval (fourier 1 z) =
      ((‖p.eval (fourier 1 z)‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_pow] using! (RCLike.conj_mul (p.eval (fourier 1 z)))
  calc
    _ = (starRingEnd ℂ (laurentCirclePolynomial a z) * laurentCirclePolynomial b z) *
        (starRingEnd ℂ (p.eval (fourier 1 z)) * p.eval (fourier 1 z)) := by ring
    _ = _ := by rw [hnorm]

lemma weightedLaurentL2_projection_line {p : Polynomial ℂ} {K : ℝ}
    (hp : HasPolynomialCircleProjectionBound p K) (hK : 1 ≤ K) (a b : ℤ →₀ ℂ)
    (ha : ∀ m : ℤ, m < 0 → a m = 0) (hb : ∀ m : ℤ, 0 ≤ m → b m = 0)
    (t : ℂ) : ‖weightedLaurentL2 p a‖ ≤
      K * ‖weightedLaurentL2 p a + t • weightedLaurentL2 p b‖ := by
  have hfilter : (a + t • b).filter (fun m => 0 ≤ m) = a := by
    ext m
    by_cases hm : 0 ≤ m
    · simp [hm, hb m hm]
    · simp [hm, ha m (lt_of_not_ge hm)]
  have he := hp (a + t • b)
  change polynomialCircleEnergy p ((a + t • b).filter (fun m => 0 ≤ m)) ≤
    K ^ 2 * polynomialCircleEnergy p (a + t • b) at he
  rw [hfilter, ← weightedLaurentL2_norm_sq, ← weightedLaurentL2_norm_sq,
    weightedLaurentL2_add_smul] at he
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (le_trans zero_le_one hK) (norm_nonneg _))).mp
  simpa only [mul_pow] using he

/-- Finite analytic and strictly negative Laurent polynomials have the exact
squared angle bound supplied by the weighted nonnegative-frequency projection. -/
theorem weightedPolynomialAngle_sq {p : Polynomial ℂ} {K : ℝ}
    (hp : HasPolynomialCircleProjectionBound p K) (hK : 1 ≤ K) (a b : ℤ →₀ ℂ)
    (ha : ∀ m : ℤ, m < 0 → a m = 0) (hb : ∀ m : ℤ, 0 ≤ m → b m = 0) :
    ‖polynomialCirclePairing p a b‖ ^ 2 ≤
      (1 - K⁻¹ ^ 2) * polynomialCircleEnergy p a * polynomialCircleEnergy p b := by
  have he := projectionAngle_sq hK (weightedLaurentL2 p a) (weightedLaurentL2 p b)
    (weightedLaurentL2_projection_line hp hK a b ha hb)
  simpa only [weightedLaurentL2_inner, weightedLaurentL2_norm_sq] using he

/-- The finite weighted angle inequality in norm form. -/
theorem weightedPolynomialAngle {p : Polynomial ℂ} {K : ℝ}
    (hp : HasPolynomialCircleProjectionBound p K) (hK : 1 ≤ K) (a b : ℤ →₀ ℂ)
    (ha : ∀ m : ℤ, m < 0 → a m = 0) (hb : ∀ m : ℤ, 0 ≤ m → b m = 0) :
    ‖polynomialCirclePairing p a b‖ ≤ Real.sqrt (1 - K⁻¹ ^ 2) *
      Real.sqrt (polynomialCircleEnergy p a) * Real.sqrt (polynomialCircleEnergy p b) := by
  have he := projectionAngle hK (weightedLaurentL2 p a) (weightedLaurentL2 p b)
    (weightedLaurentL2_projection_line hp hK a b ha hb)
  simpa only [weightedLaurentL2_inner, weightedLaurentL2_norm] using he

end ProofProject
