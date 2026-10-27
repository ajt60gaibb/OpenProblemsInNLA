import NLA.Proofs.IE22.EnergyBounds
import NLA.Proofs.IE22.GaussianBasics
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace NLA.Proofs.IE22

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Integral Cauchy--Schwarz in a squared real form. -/
theorem integral_mul_sq_le (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ ω, f ω * g ω ∂μ) ^ 2 ≤
      (∫ ω, (f ω) ^ 2 ∂μ) * (∫ ω, (g ω) ^ 2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa only [ENNReal.ofReal_ofNat] using hf)
    (by simpa only [ENNReal.ofReal_ofNat] using hg)
  have hnorm : |∫ ω, f ω * g ω ∂μ| ≤ ∫ ω, ‖f ω‖ * ‖g ω‖ ∂μ := by
    simpa only [Real.norm_eq_abs, norm_mul] using
      (norm_integral_le_integral_norm (fun ω => f ω * g ω))
  have h' : |∫ ω, f ω * g ω ∂μ| ≤
      Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
    apply hnorm.trans
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs, ← Real.sqrt_eq_rpow] using h
  have hposf : 0 ≤ ∫ ω, f ω ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hposg : 0 ≤ ∫ ω, g ω ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hs := sq_le_sq₀ (abs_nonneg (∫ ω, f ω * g ω ∂μ))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) |>.2 h'
  simpa only [sq_abs, mul_pow, Real.sq_sqrt hposf, Real.sq_sqrt hposg] using hs

/-- Variance is no larger than the squared distance from a fixed constant. -/
theorem variance_le_integral_sub_sq [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) (c : ℝ) :
    Var[X; μ] ≤ ∫ ω, (X ω - c) ^ 2 ∂μ := by
  simpa only [variance_sub_const hX.1, Pi.pow_apply] using
    (variance_le_expectation_sq (μ := μ) (X := fun ω => X ω - c)
      (hX.aestronglyMeasurable.sub aestronglyMeasurable_const))

/-- Real Lipschitz maps preserve L2 under a probability measure. -/
theorem memLp_comp_lipschitz [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) {L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) : MemLp (f ∘ X) 2 μ := by
  have hz : LipschitzWith L (fun x => f x - f 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using hf.dist_le_mul x y
  have h := hz.comp_memLp (by simp) hX
  convert h.add (memLp_const (f 0)) using 1
  ext ω
  simp

/-- A real Lipschitz function contracts variance by the square of its constant. -/
theorem variance_comp_lipschitz [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) {L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) : Var[f ∘ X; μ] ≤ (L : ℝ)^2 * Var[X; μ] := by
  have hfx := memLp_comp_lipschitz hX hf
  calc
    Var[f ∘ X; μ] ≤ ∫ ω, (f (X ω) - f (μ[X]))^2 ∂μ :=
      variance_le_integral_sub_sq hfx _
    _ ≤ ∫ ω, (L : ℝ)^2 * (X ω - μ[X])^2 ∂μ := by
      apply integral_mono ((hfx.sub (memLp_const _)).integrable_sq)
        (((hX.sub (memLp_const _)).integrable_sq).const_mul _)
      intro ω
      have h := hf.norm_sub_le (X ω) (μ[X])
      have hs := sq_le_sq₀ (norm_nonneg (f (X ω) - f (μ[X])))
        (mul_nonneg L.coe_nonneg (norm_nonneg (X ω - μ[X]))) |>.2 h
      simpa only [Pi.sub_apply, Function.comp_apply, Real.norm_eq_abs, mul_pow, sq_abs] using hs
    _ = (L : ℝ)^2 * Var[X; μ] := by
      rw [integral_const_mul, variance_eq_integral hX.aemeasurable]

/-- Squared Cauchy--Schwarz for covariance, with an uncentered second factor. -/
theorem covariance_sq_le_variance_mul_integral_sq [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[X, Y; μ] ^2 ≤ Var[X; μ] * ∫ ω, (Y ω)^2 ∂μ := by
  have hcenter : ∫ ω, (X ω - μ[X]) * Y ω ∂μ = cov[X,Y;μ] := by
    rw [covariance_eq_sub hX hY]
    simp_rw [sub_mul]
    change (∫ ω, (X * Y) ω - μ[X] * Y ω ∂μ) = _
    rw [integral_sub (hX.integrable_mul hY) ((hY.integrable (by simp)).const_mul _),
      integral_const_mul]
  have h := integral_mul_sq_le (fun ω => X ω - μ[X]) Y (hX.sub (memLp_const _)) hY
  rw [hcenter, ← variance_eq_integral hX.aemeasurable] at h
  exact h

/-- The Gaussian residual is genuinely independent; its distribution need not
coincide with the second original marginal. -/
theorem gaussian_indep_residual [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) μ)
    (hv : Var[X; μ] ≠ 0) :
    IndepFun X (fun ω => Y ω - (cov[X,Y;μ] / Var[X;μ]) * X ω) μ := by
  let c := cov[X,Y;μ] / Var[X;μ]
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ) - c • ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hpair := hXY.map L
  change HasGaussianLaw (fun ω => (X ω, Y ω - c * X ω)) μ at hpair
  apply hpair.indepFun_of_covariance_eq_zero
  rw [covariance_fun_sub_right hXY.fst.memLp_two hXY.snd.memLp_two
    (hXY.fst.memLp_two.const_mul c), covariance_const_mul_right,
    covariance_self hXY.fst.aemeasurable]
  dsimp [c]
  field_simp
  ring

/-- An actual centered Gaussian covariance estimate. It requires no derivatives
or Gaussian Poincare premise. -/
theorem abs_covariance_comp_lipschitz [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) μ)
    (hmean : μ[X] = 0) {Lf Lg : NNReal} {f g : ℝ → ℝ}
    (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g) :
    |cov[f ∘ X, g ∘ Y; μ]| ≤ (Lf : ℝ) * (Lg : ℝ) * |cov[X,Y;μ]| := by
  have hX := hXY.fst.memLp_two
  have hY := hXY.snd.memLp_two
  have hfX := memLp_comp_lipschitz hX hf
  have hgY := memLp_comp_lipschitz hY hg
  by_cases hv : Var[X;μ] = 0
  · have hconst := ae_eq_integral_of_variance_eq_zero hX hv
    have hfc : (f ∘ X) =ᵐ[μ] fun _ => f 0 := by
      filter_upwards [hconst] with ω hω
      simp [Function.comp_apply, hω, hmean]
    have hcov : cov[f ∘ X,g ∘ Y;μ] = 0 := by
      simp only [covariance]
      have heq : μ[f ∘ X] = f 0 := by rw [integral_congr_ae hfc]; simp
      rw [heq]
      apply integral_eq_zero_of_ae
      filter_upwards [hfc] with ω hω
      change (f ∘ X) ω = f 0 at hω
      change ((f ∘ X) ω - f 0) * _ = 0
      rw [hω, sub_self, zero_mul]
    rw [hcov, abs_zero]
    positivity
  have hvpos : 0 < Var[X;μ] := lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hv)
  let c := cov[X,Y;μ] / Var[X;μ]
  let Y' : Ω → ℝ := fun ω => Y ω - c * X ω
  have hY' : MemLp Y' 2 μ := hY.sub (hX.const_mul c)
  have hgY' := memLp_comp_lipschitz hY' hg
  have hind : IndepFun X Y' μ := gaussian_indep_residual hXY hv
  have hzero : cov[f ∘ X, g ∘ Y'; μ] = 0 :=
    (hind.comp hf.continuous.measurable hg.continuous.measurable).covariance_eq_zero hfX hgY'
  have hcov : cov[f ∘ X, g ∘ Y;μ] = cov[f ∘ X, (g ∘ Y) - (g ∘ Y');μ] := by
    rw [covariance_sub_right hfX hgY hgY', hzero, sub_zero]
  have hdiff : ∫ ω, ((g ∘ Y) ω - (g ∘ Y') ω)^2 ∂μ ≤
      (Lg : ℝ)^2 * c^2 * Var[X;μ] := by
    calc
      _ ≤ ∫ ω, (Lg : ℝ)^2 * c^2 * (X ω)^2 ∂μ := by
        apply integral_mono ((hgY.sub hgY').integrable_sq)
          (hX.integrable_sq.const_mul _)
        intro ω
        have h := hg.norm_sub_le (Y ω) (Y' ω)
        have hs := sq_le_sq₀ (norm_nonneg (g (Y ω)-g (Y' ω)))
          (mul_nonneg Lg.coe_nonneg (norm_nonneg (Y ω - Y' ω))) |>.2 h
        have heq : Y ω - Y' ω = c * X ω := by dsimp [Y']; ring
        simpa only [Pi.sub_apply, Function.comp_apply, Real.norm_eq_abs, mul_pow, sq_abs, heq, mul_assoc] using hs
      _ = _ := by
        rw [integral_const_mul, variance_of_integral_eq_zero hX.aemeasurable hmean]
  have hcs := covariance_sq_le_variance_mul_integral_sq hfX (hgY.sub hgY')
  rw [← hcov] at hcs
  have hvf := variance_comp_lipschitz hX hf
  have hsq : cov[f ∘ X,g ∘ Y;μ] ^2 ≤
      ((Lf : ℝ) * (Lg : ℝ) * |cov[X,Y;μ]|)^2 := by
    calc
      _ ≤ Var[f ∘ X;μ] * ((Lg : ℝ)^2 * c^2 * Var[X;μ]) :=
        hcs.trans (mul_le_mul_of_nonneg_left hdiff (variance_nonneg _ _))
      _ ≤ ((Lf : ℝ)^2 * Var[X;μ]) * ((Lg : ℝ)^2 * c^2 * Var[X;μ]) :=
        mul_le_mul_of_nonneg_right hvf (by positivity)
      _ = _ := by
        dsimp [c]
        rw [mul_pow, mul_pow, sq_abs, div_pow]
        field_simp
  apply (sq_le_sq₀ (abs_nonneg (cov[f ∘ X,g ∘ Y;μ]))
    (show 0 ≤ (Lf : ℝ) * (Lg : ℝ) * |cov[X,Y;μ]| by positivity)).1
  simpa only [sq_abs] using hsq

/-- The bounded quadratic hinge is globally Lipschitz, including its corners. -/
theorem hinge_lipschitz {t : ℝ} (ht : 0 ≤ t) :
    LipschitzWith (2 * Real.sqrt t).toNNReal (hinge t) := by
  let R := Real.sqrt t
  have hR : 0 ≤ R := Real.sqrt_nonneg t
  have hR2 : R^2 = t := Real.sq_sqrt ht
  have heq (x : ℝ) : hinge t x = t - (min |x| R)^2 := by
    by_cases hx : |x| ≤ R
    · have hx2 : x^2 ≤ t := by
        have := (sq_le_sq₀ (abs_nonneg x) hR).2 hx
        nlinarith [sq_abs x]
      simp [hinge, min_eq_left hx, max_eq_left (sub_nonneg.mpr hx2), sq_abs]
    · have hxR : R ≤ |x| := le_of_not_ge hx
      have hx2 : t ≤ x^2 := by nlinarith [sq_abs x]
      simp [hinge, min_eq_right hxR, max_eq_right (sub_nonpos.mpr hx2), hR2]
  have hu : LipschitzWith 1 (fun x : ℝ => min |x| R) := by
    simpa only [Real.norm_eq_abs] using ((lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)).min_const R)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, heq x, heq y]
  have hx0 : 0 ≤ min |x| R := le_min (abs_nonneg _) hR
  have hy0 : 0 ≤ min |y| R := le_min (abs_nonneg _) hR
  have hxR : min |x| R ≤ R := min_le_right _ _
  have hyR : min |y| R ≤ R := min_le_right _ _
  have hsum : |min |x| R + min |y| R| ≤ 2*R := by
    rw [abs_of_nonneg (add_nonneg hx0 hy0)]
    linarith
  have hdiff : |min |x| R - min |y| R| ≤ |x-y| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hu.dist_le_mul x y
  have hid : (t-(min |x| R)^2) - (t-(min |y| R)^2) =
      -((min |x| R - min |y| R) * (min |x| R + min |y| R)) := by ring
  rw [hid, abs_neg, abs_mul, Real.toNNReal_of_nonneg (mul_nonneg (by norm_num) hR)]
  change _ ≤ (2*R) * |x-y|
  calc
    _ ≤ |x-y| * (2*R) := mul_le_mul hdiff hsum (abs_nonneg _) (abs_nonneg _)
    _ = _ := mul_comm _ _

/-- Hinge covariance for centered actual Gaussian linear observations. -/
theorem abs_covariance_hinge [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) μ)
    (hmean : μ[X] = 0) {t : ℝ} (ht : 0 ≤ t) :
    |cov[hinge t ∘ X, hinge t ∘ Y; μ]| ≤ 4*t*|cov[X,Y;μ]| := by
  have h := abs_covariance_comp_lipschitz hXY hmean (hinge_lipschitz ht) (hinge_lipschitz ht)
  rw [Real.toNNReal_of_nonneg (by positivity : 0 ≤ 2*Real.sqrt t)] at h
  have heq : (2*Real.sqrt t)*(2*Real.sqrt t) = 4*t := by nlinarith [Real.sq_sqrt ht]
  change |cov[hinge t ∘ X, hinge t ∘ Y; μ]| ≤
    (2*Real.sqrt t)*(2*Real.sqrt t)*|cov[X,Y;μ]| at h
  rw [heq] at h
  exact h

/-- The finite correlated-row hinge sum is controlled by the genuine
absolute covariance matrix of its Gaussian observations. -/
theorem variance_hinge_sum_le [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ)
    (hGaussian : ∀ i j, HasGaussianLaw (fun ω => (X i ω, X j ω)) μ)
    (hmean : ∀ i, μ[X i] = 0) {t : ℝ} (ht : 0 ≤ t) :
    Var[fun ω => ∑ i, hinge t (X i ω); μ] ≤
      4*t*∑ i, ∑ j, |cov[X i,X j;μ]| := by
  have hmem : ∀ i, MemLp (hinge t ∘ X i) 2 μ := fun i =>
    memLp_comp_lipschitz (hGaussian i i).fst.memLp_two (hinge_lipschitz ht)
  change Var[fun ω => ∑ i, (hinge t ∘ X i) ω; μ] ≤ _
  rw [variance_fun_sum hmem]
  calc
    _ ≤ ∑ i, ∑ j, 4*t*|cov[X i,X j;μ]| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact (le_abs_self _).trans (abs_covariance_hinge (hGaussian i j) (hmean i) ht)
    _ = _ := by simp only [Finset.mul_sum]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Two actual Gaussian linear observations have a genuine joint Gaussian law. -/
theorem gaussian_inner_pair_law {n : ℕ} (v w : Euclid n) :
    HasGaussianLaw (fun g : Euclid n => (inner ℝ v g, inner ℝ w g))
      (stdGaussian (Euclid n)) := by
  convert! (IsGaussian.hasGaussianLaw_id (μ := stdGaussian (Euclid n))).map
      ((innerSL ℝ v).prod (innerSL ℝ w)) using 1

/-- Covariance of the actual Gaussian linear observations is their Euclidean Gram entry. -/
theorem gaussian_inner_covariance {n : ℕ} (v w : Euclid n) :
    cov[(fun g : Euclid n => inner ℝ v g), (fun g => inner ℝ w g);
      stdGaussian (Euclid n)] = inner ℝ v w := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian]
  rfl

/-- Actual finite correlated Gaussian rows obey the Gram covariance bound. -/
theorem variance_gaussian_rows_hinge_le {n : ℕ} {ι : Type*} [Fintype ι]
    (b : ι → Euclid n) {t : ℝ} (ht : 0 ≤ t) :
    Var[(fun g : Euclid n => ∑ i, hinge t (inner ℝ (b i) g));
      stdGaussian (Euclid n)] ≤ 4*t*∑ i, ∑ j, |inner ℝ (b i) (b j)| := by
  have h := variance_hinge_sum_le (μ := stdGaussian (Euclid n))
    (fun i g => inner ℝ (b i) g) (fun i j => gaussian_inner_pair_law (b i) (b j))
    (fun i => gaussian_inner_mean (b i)) ht
  simpa only [gaussian_inner_covariance] using h

#assert_trust kernel gaussian_inner_pair_law
#assert_trust kernel gaussian_inner_covariance
#assert_trust kernel variance_gaussian_rows_hinge_le
#assert_trust kernel variance_hinge_sum_le
#assert_trust kernel hinge_lipschitz
#assert_trust kernel abs_covariance_hinge
#assert_trust kernel abs_covariance_comp_lipschitz
#print axioms abs_covariance_comp_lipschitz
end NLA.Proofs.IE22
