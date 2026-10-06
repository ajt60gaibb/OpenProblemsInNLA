/-
Exact Gaussian probe comparison and rectangular inverse operator moments.
The mathematical contract and prior independent approval are recorded in
reviews/gaussian-operator-inverse-specification.md. All norms below are actual
Euclidean operator norms. No Gaussian estimate is assumed.
-/
import NLA.IE06.GaussianRegression
import NLA.IE06.Spectral
import NLA.IE06.GaussianOvercrowdingScalars

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
namespace NLA.IE06.GaussianOperatorInverse
open GaussianNull GaussianQuadratic GaussianRegression
local instance matrixBorelSpace (d : ℕ) : BorelSpace (Mat d) :=
  inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))
local instance gaussianRect_probability (m n : ℕ) : IsProbabilityMeasure (gaussianRect m n) := by
  unfold gaussianRect
  infer_instance

def quadratic {m : ℕ} (H : Mat m) (z : E m) : ℝ :=
  ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m) H z⟫

theorem quadratic_eq_dot {m : ℕ} (H : Mat m) (z : E m) :
    quadratic H z = ofLp z ⬝ᵥ (H *ᵥ ofLp z) :=
  Matrix.inner_toEuclideanCLM H z z

theorem quadratic_nonneg {m : ℕ} {H : Mat m} (hH : H.PosSemidef) (z : E m) :
    0 ≤ quadratic H z := by
  simpa only [quadratic_eq_dot, star_trivial] using hH.dotProduct_mulVec_nonneg (ofLp z)

theorem quadratic_abs_le {m : ℕ} (H : Mat m) (z : E m) :
    |quadratic H z| ≤ Spectral.opNorm H * ‖z‖ ^ 2 := by
  calc
    _ ≤ ‖z‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m) H z‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖z‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m) H‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m) H).le_opNorm z) (norm_nonneg z)
    _ = _ := by change _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m) H‖ * ‖z‖ ^ 2; ring

theorem quadratic_power_integrable {m : ℕ} (H : Mat m) (q : ℕ) :
    Integrable (fun z : E m => quadratic H z ^ q) (stdGaussian (E m)) := by
  have hc : Continuous (fun z : E m => quadratic H z ^ q) := by unfold quadratic; fun_prop
  apply ((GaussianSmallest.gaussian_norm_moment m q).1.const_mul
    (Spectral.opNorm H ^ q)).mono' hc.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_pow]
  calc
    |quadratic H z| ^ q ≤ (Spectral.opNorm H * ‖z‖ ^ 2) ^ q :=
      pow_le_pow_left₀ (abs_nonneg _) (quadratic_abs_le H z) q
    _ = _ := by rw [mul_pow, ← pow_mul]

theorem psd_exists_eigenvalue_eq_opNorm {m : ℕ} (hm : 0 < m) {H : Mat m}
    (hH : H.PosSemidef) : ∃ i : Fin m, hH.isHermitian.eigenvalues i = Spectral.opNorm H := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hn : Spectral.opNorm H = ‖hH.isHermitian.eigenvalues‖ := by
    rw [Spectral.opNorm_eq_l2]
    conv_lhs => rw [hH.isHermitian.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
    rfl
  obtain ⟨⟨i, hi⟩, _⟩ := IsGreatest.pi_norm hH.isHermitian.eigenvalues
  refine ⟨i, ?_⟩
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hH.eigenvalues_nonneg i), ← hn] using hi

theorem gaussian_coordinate_even_moment {m : ℕ} (i : Fin m) (q : ℕ) :
    Integrable (fun z : Fin m → ℝ => z i ^ (2 * q)) (gaussianVector m) ∧
    (∫ z : Fin m → ℝ, z i ^ (2 * q) ∂gaussianVector m) =
      ∏ j ∈ Finset.range q, (1 + 2 * (j : ℝ)) := by
  let f : ℝ → ℝ := fun x => x ^ (2 * q)
  have hf : AEStronglyMeasurable f (gaussianReal 0 1) := by fun_prop
  have hmp1 : MeasurePreserving (Function.eval (0 : Fin 1)) (gaussianVector 1)
      (gaussianReal 0 1) := measurePreserving_eval (μ := fun _ : Fin 1 => gaussianReal 0 1) 0
  obtain ⟨hi, he⟩ := GaussianSmallest.gaussian_sumSquares_moment 1 q
  have heq : (fun z : Fin 1 → ℝ => GaussianSmallest.sumSquares z ^ q) =
      f ∘ Function.eval 0 := by
    funext z
    simp [GaussianSmallest.sumSquares, f, ← pow_mul]
  rw [heq] at hi he
  have hfi : Integrable f (gaussianReal 0 1) := (hmp1.integrable_comp hf).mp hi
  have hfe : (∫ x, f x ∂gaussianReal 0 1) =
      ∏ j ∈ Finset.range q, (1 + 2 * (j : ℝ)) := by
    rw [← hmp1.map_eq, integral_map hmp1.measurable.aemeasurable (by fun_prop)]
    simpa only [Function.comp_def, Nat.cast_one] using he
  have hmp : MeasurePreserving (Function.eval i) (gaussianVector m) (gaussianReal 0 1) :=
    measurePreserving_eval (μ := fun _ : Fin m => gaussianReal 0 1) i
  refine ⟨hmp.integrable_comp_of_integrable hfi, ?_⟩
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by fun_prop)] at hfe
  exact hfe

/-- A fixed positive semidefinite quadratic form contains at least one
top-eigenvalue Gaussian coordinate. This retains the full odd-factorial gain. -/
theorem gaussian_probe_lower {m : ℕ} (hm : 0 < m) {H : Mat m}
    (hH : H.PosSemidef) (q : ℕ) :
    (∏ j ∈ Finset.range q, (1 + 2 * (j : ℝ))) * Spectral.opNorm H ^ q ≤
      ∫ z : E m, quadratic H z ^ q ∂stdGaussian (E m) := by
  let b := hH.isHermitian.eigenvectorBasis
  let rot : (Fin m → ℝ) → E m := fun z => b.repr.symm (toLp 2 z)
  have hmp : MeasurePreserving rot (gaussianVector m) (stdGaussian (E m)) := by
    exact (show MeasurePreserving b.repr.symm (stdGaussian (E m)) (stdGaussian (E m))
      from ⟨by fun_prop, stdGaussian_map b.repr.symm⟩).comp
      ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have hdiag (z : Fin m → ℝ) :
      quadratic H (rot z) = ∑ j, hH.isHermitian.eigenvalues j * z j ^ 2 := by
    let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m) H
    have hT (i : Fin m) : T (b i) = hH.isHermitian.eigenvalues i • b i := by
      apply (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).injective
      exact hH.isHermitian.mulVec_eigenvectorBasis i
    have hrot : rot z = ∑ i, z i • b i := by
      exact (b.sum_repr (b.repr.symm (toLp 2 z))).symm.trans (by simp)
    rw [quadratic, hrot]
    change ⟪(∑ i, z i • b i), T (∑ i, z i • b i)⟫ = _
    simp_rw [map_sum, map_smul, hT, smul_smul, inner_sum, sum_inner,
      real_inner_smul_left, real_inner_smul_right, b.inner_eq_ite]
    simp [pow_two, mul_assoc, mul_comm, mul_left_comm]
  obtain ⟨i, hi⟩ := psd_exists_eigenvalue_eq_opNorm hm hH
  have hlo (z : Fin m → ℝ) :
      Spectral.opNorm H ^ q * z i ^ (2 * q) ≤ quadratic H (rot z) ^ q := by
    rw [pow_mul, ← mul_pow, hdiag, ← hi]
    exact pow_le_pow_left₀ (mul_nonneg (hH.eigenvalues_nonneg i) (sq_nonneg (z i))) (Finset.single_le_sum
      (fun j _ => mul_nonneg (hH.eigenvalues_nonneg j) (sq_nonneg (z j)))
      (Finset.mem_univ i)) q
  obtain ⟨hci, hce⟩ := gaussian_coordinate_even_moment i q
  have hqi := hmp.integrable_comp_of_integrable (quadratic_power_integrable H q)
  have hbound := integral_mono (hci.const_mul (Spectral.opNorm H ^ q)) hqi hlo
  rw [integral_const_mul, hce] at hbound
  have hmap : (∫ z, quadratic H (rot z) ^ q ∂gaussianVector m) =
      ∫ z : E m, quadratic H z ^ q ∂stdGaussian (E m) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by unfold quadratic; fun_prop)]
  simpa only [mul_comm, Function.comp_def, hmap] using hbound

theorem odd_moment_pos (q : ℕ) : 0 < ∏ j ∈ Finset.range q, (1 + 2 * (j : ℝ)) := by
  exact Finset.prod_pos fun j _ => by positivity

theorem inverse_denominator_pos {m n q : ℕ} (_hm : 0 < m) (hn : m + 2 * q ≤ n) :
    0 < ∏ j ∈ Finset.range q, (((n - m + 1 : ℕ) : ℝ) - 2 * (j + 1)) := by
  apply Finset.prod_pos
  intro j hj
  exact GaussianSmallest.inverse_moment_factor_pos (n - m + 1) q j (by omega)
    (Finset.mem_range.mp hj)

theorem inverse_gram_quadratic_nonneg {m n : ℕ} (G : RectMat m n) (z : E m) :
    0 ≤ directionalQuadratic G z := by
  rw [directionalQuadratic, ← quadratic_eq_dot]
  exact quadratic_nonneg (Matrix.posSemidef_self_mul_conjTranspose (Matrix.of G)).inv z

theorem inverse_gram_opNorm_measurable (m n : ℕ) :
    Measurable (fun G : RectMat m n => Spectral.opNorm (gram G)⁻¹) := by
  have hc : Continuous (Spectral.opNorm : Mat m → ℝ) := by
    change Continuous (fun H : Mat m => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m) H‖)
    exact continuous_norm.comp
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  exact hc.measurable.comp ((measurable_inverse m).comp gram_continuous.measurable)

theorem directionalQuadratic_joint_measurable (m n : ℕ) :
    Measurable (fun z : E m × RectMat m n => directionalQuadratic z.2 z.1) := by
  unfold directionalQuadratic Matrix.mulVec dotProduct
  have hInv : Measurable (fun z : E m × RectMat m n => (gram z.2)⁻¹) :=
    (measurable_inverse m).comp (gram_continuous.measurable.comp measurable_snd)
  fun_prop

/-- The sharp directional regression moment is integrated against an
independent Gaussian probe before the operator norm comparison is made. -/
theorem inverse_gram_opNorm_moment {m n q : ℕ} (hm : 0 < m) (hn : m + 2 * q ≤ n) :
    Integrable (fun G : RectMat m n => Spectral.opNorm (gram G)⁻¹ ^ q) (gaussianRect m n) ∧
    (∫ G : RectMat m n, Spectral.opNorm (gram G)⁻¹ ^ q ∂gaussianRect m n) ≤
      (∏ j ∈ Finset.range q, ((m : ℝ) + 2 * j)) /
        ((∏ j ∈ Finset.range q, (1 + 2 * (j : ℝ))) *
          ∏ j ∈ Finset.range q, (((n - m + 1 : ℕ) : ℝ) - 2 * (j + 1))) := by
  let D : ℝ := ∏ j ∈ Finset.range q, (1 + 2 * (j : ℝ))
  let P : ℝ := ∏ j ∈ Finset.range q, (((n - m + 1 : ℕ) : ℝ) - 2 * (j + 1))
  have hD : 0 < D := odd_moment_pos q
  have hP : 0 < P := inverse_denominator_pos hm hn
  let F : E m × RectMat m n → ℝ := fun z => directionalQuadratic z.2 z.1 ^ q
  have hFm : Measurable F := (directionalQuadratic_joint_measurable m n).pow_const q
  have hFn (z : E m × RectMat m n) : 0 ≤ F z :=
    pow_nonneg (inverse_gram_quadratic_nonneg _ _) q
  have hFint : Integrable F ((stdGaussian (E m)).prod (gaussianRect m n)) := by
    apply (integrable_prod_iff hFm.aestronglyMeasurable).mpr
    constructor
    · exact Filter.Eventually.of_forall fun z => (directional_inverse_gram_moment hm hn z).1
    · have heq (z : E m) : (∫ G, ‖F (z, G)‖ ∂gaussianRect m n) = ‖z‖ ^ (2 * q) / P := by
        simp only [Real.norm_eq_abs, abs_of_nonneg (hFn _)]
        exact (directional_inverse_gram_moment hm hn z).2
      simp_rw [heq]
      exact (GaussianSmallest.gaussian_norm_moment m q).1.div_const P
  let I : RectMat m n → ℝ := fun G => ∫ z : E m, F (z, G) ∂stdGaussian (E m)
  have hIi : Integrable I (gaussianRect m n) := hFint.integral_prod_right
  have hIn (G : RectMat m n) : 0 ≤ I G := integral_nonneg fun z => hFn (z, G)
  have hlo (G : RectMat m n) : D * Spectral.opNorm (gram G)⁻¹ ^ q ≤ I G := by
    have hh := gaussian_probe_lower hm
      (Matrix.posSemidef_self_mul_conjTranspose (Matrix.of G)).inv q
    simpa only [quadratic_eq_dot, GaussianRegression.gram, directionalQuadratic, I, F, D] using hh
  have hoi : Integrable (fun G : RectMat m n => Spectral.opNorm (gram G)⁻¹ ^ q)
      (gaussianRect m n) := by
    apply (hIi.div_const D).mono' ((inverse_gram_opNorm_measurable m n).pow_const q).aestronglyMeasurable
    filter_upwards [] with G
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Spectral.opNorm_nonneg _) q)]
    exact (le_div_iff₀ hD).mpr (by simpa only [mul_comm] using hlo G)
  have hIe : (∫ G, I G ∂gaussianRect m n) =
      (∏ j ∈ Finset.range q, ((m : ℝ) + 2 * j)) / P := by
    rw [show (∫ G, I G ∂gaussianRect m n) =
      ∫ z : E m, ∫ G : RectMat m n, F (z, G) ∂gaussianRect m n ∂stdGaussian (E m) from
        (integral_integral_swap hFint).symm]
    simp_rw [show ∀ z : E m, (∫ G, F (z, G) ∂gaussianRect m n) = ‖z‖ ^ (2 * q) / P from
      fun z => (directional_inverse_gram_moment hm hn z).2]
    rw [integral_div, (GaussianSmallest.gaussian_norm_moment m q).2]
  refine ⟨hoi, ?_⟩
  have hh := integral_mono (hoi.const_mul D) hIi hlo
  rw [integral_const_mul, hIe] at hh
  change _ ≤ _ / (D * P)
  calc
    _ ≤ ((∏ j ∈ Finset.range q, ((m : ℝ) + 2 * j)) / P) / D :=
      (le_div_iff₀ hD).mpr (by simpa only [mul_comm] using hh)
    _ = _ := by rw [div_div, mul_comm P D]

theorem odd_moment_ge_factorial (r : ℕ) :
    (r.factorial : ℝ) ≤ ∏ j ∈ Finset.range r, (1 + 2 * (j : ℝ)) := by
  rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]
  apply Finset.prod_le_prod
  · intro j _; positivity
  · intro j _; push_cast; nlinarith [show 0 ≤ (j : ℝ) by positivity]

theorem radial_moment_le {m r : ℕ} (hmr : m ≤ r) :
    (∏ j ∈ Finset.range r, ((m : ℝ) + 2 * j)) ≤ (3 * (r : ℝ)) ^ r := by
  calc
    _ ≤ ∏ _j ∈ Finset.range r, (3 * (r : ℝ)) := by
      apply Finset.prod_le_prod
      · intro j _; positivity
      · intro j hj
        have hj' : (j : ℝ) ≤ r := by exact_mod_cast (Finset.mem_range.mp hj).le
        have hm' : (m : ℝ) ≤ r := by exact_mod_cast hmr
        linarith
    _ = _ := by simp

theorem inverse_denominator_ge_odd {m n r : ℕ} (hmr : m ≤ r) (hn : 3 * r ≤ n) :
    (∏ j ∈ Finset.range r, (1 + 2 * (j : ℝ))) ≤
      ∏ j ∈ Finset.range r, (((n - m + 1 : ℕ) : ℝ) - 2 * (j + 1)) := by
  rw [← Finset.prod_range_reflect (fun j : ℕ => (1 + 2 * (j : ℝ))) r]
  apply Finset.prod_le_prod
  · intro j _; positivity
  · intro j hj
    have hjr := Finset.mem_range.mp hj
    have hd : 2 * r + 1 ≤ n - m + 1 := by omega
    have hj : r - 1 - j + j + 1 = r := by omega
    have hd' : (2 : ℝ) * r + 1 ≤ (n - m + 1 : ℕ) := by exact_mod_cast hd
    have hj' : ((r - 1 - j : ℕ) : ℝ) + j + 1 = r := by exact_mod_cast hj
    linarith

theorem inverse_gram_opNorm_moment_bound {m n r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hmr : m ≤ r) (hn : 3 * r ≤ n) :
    Integrable (fun G : RectMat m n => Spectral.opNorm (gram G)⁻¹ ^ r) (gaussianRect m n) ∧
    (∫ G : RectMat m n, Spectral.opNorm (gram G)⁻¹ ^ r ∂gaussianRect m n) ≤
      (3 * Real.exp 2 / r) ^ r := by
  obtain ⟨hi, he⟩ := inverse_gram_opNorm_moment hm (show m + 2 * r ≤ n by omega)
  refine ⟨hi, he.trans ?_⟩
  let D : ℝ := ∏ j ∈ Finset.range r, (1 + 2 * (j : ℝ))
  let P : ℝ := ∏ j ∈ Finset.range r, (((n - m + 1 : ℕ) : ℝ) - 2 * (j + 1))
  have hD : 0 < D := odd_moment_pos r
  have hP : 0 < P := inverse_denominator_pos hm (by omega)
  have hFD : (r.factorial : ℝ) ≤ D := odd_moment_ge_factorial r
  have hDP : D ≤ P := inverse_denominator_ge_odd hmr hn
  have hF : 0 < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
  have hiD : D⁻¹ ≤ (Real.exp 1 / r) ^ r :=
    (inv_anti₀ hF hFD).trans (GaussianOvercrowdingScalars.factorial_inverse_le hr)
  have hiP : P⁻¹ ≤ (Real.exp 1 / r) ^ r := (inv_anti₀ hD hDP).trans hiD
  change _ / (D * P) ≤ _
  calc
    _ = (∏ j ∈ Finset.range r, ((m : ℝ) + 2 * j)) * D⁻¹ * P⁻¹ := by
      rw [div_eq_mul_inv, _root_.mul_inv_rev]; ring
    _ ≤ (3 * (r : ℝ)) ^ r * (Real.exp 1 / r) ^ r * (Real.exp 1 / r) ^ r := by
      gcongr
      exact radial_moment_le hmr
    _ = _ := by
      rw [← mul_pow, ← mul_pow]
      congr 1
      have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [he2]
      have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
      field_simp

/-- Operator tail for the ordinary inverse Gram matrix; full row rank holds
almost everywhere under these dimension assumptions. -/
theorem inverse_gram_opNorm_tail {m n r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hmr : m ≤ r) (hn : 3 * r ≤ n) (x : ℝ) :
    gaussianRect m n {G | 3 * Real.exp (2 + x / r) / r < Spectral.opNorm (gram G)⁻¹} ≤
      ENNReal.ofReal (Real.exp (-x)) := by
  obtain ⟨hi, he⟩ := inverse_gram_opNorm_moment_bound hm hr hmr hn
  let a : ℝ := 3 * Real.exp (2 + x / r) / r
  let C : ℝ := 3 * Real.exp 2 / r
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have ha : 0 < a := by dsimp [a]; positivity
  have hap : 0 < a ^ r := pow_pos ha r
  have harel : a = C * Real.exp (x / r) := by
    dsimp [a, C]
    rw [Real.exp_add]
    ring
  have hae : a ^ r * Real.exp (-x) = C ^ r := by
    rw [harel, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    have hz : (r : ℝ) * (x / r) + -x = 0 := by field_simp; ring
    rw [hz, Real.exp_zero, mul_one]
  have hmkv := mul_meas_ge_le_integral_of_nonneg
    (μ := gaussianRect m n) (f := fun G : RectMat m n => Spectral.opNorm (gram G)⁻¹ ^ r)
    (Filter.Eventually.of_forall fun G => pow_nonneg (Spectral.opNorm_nonneg _) r) hi (a ^ r)
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr
  change (gaussianRect m n).real {G | a < Spectral.opNorm (gram G)⁻¹} ≤ Real.exp (-x)
  calc
    _ ≤ (gaussianRect m n).real {G | a ^ r ≤ Spectral.opNorm (gram G)⁻¹ ^ r} :=
      measureReal_mono (fun G hG => pow_le_pow_left₀ ha.le (le_of_lt hG) r)
    _ ≤ Real.exp (-x) := by
      apply (mul_le_mul_iff_right₀ hap).mp
      exact hmkv.trans (he.trans_eq hae.symm)

/-- The rectangular Gaussian pseudoinverse bound retains inverse-r scaling
with a universal constant 3. It includes the empty-row case and uses the
genuine spectral Moore–Penrose inverse on every matrix. -/
theorem gaussian_pinv_tail {m n r : ℕ} (hr : 0 < r) (hmr : m ≤ r) (hn : 3 * r ≤ n)
    (x : ℝ) :
    gaussianRect m n {G | 3 * Real.exp (2 + x / r) / r <
      Spectral.opNorm (Spectral.pinv (Matrix.of G)) ^ 2} ≤ ENNReal.ofReal (Real.exp (-x)) := by
  by_cases hm : m = 0
  · subst m
    have hz (G : RectMat 0 n) : Spectral.opNorm (Spectral.pinv (Matrix.of G)) = 0 := by
      have hp : Spectral.pinv (Matrix.of G) = 0 := Subsingleton.elim _ _
      rw [hp]
      simp [Spectral.opNorm, Spectral.euclideanMap]
    have ha : 0 ≤ 3 * Real.exp (2 + x / r) / r := by positivity
    have he : {G : RectMat 0 n | 3 * Real.exp (2 + x / r) / r <
        Spectral.opNorm (Spectral.pinv (Matrix.of G)) ^ 2} = ∅ := by
      ext G
      simp only [Set.mem_ofPred_eq, hz, zero_pow (by decide : (2 : ℕ) ≠ 0), Set.mem_empty_iff_false,
        iff_false]
      exact not_lt_of_ge ha
    rw [he, measure_empty]
    exact bot_le
  · have heq : {G : RectMat m n | 3 * Real.exp (2 + x / r) / r <
        Spectral.opNorm (Spectral.pinv (Matrix.of G)) ^ 2} =ᵐ[gaussianRect m n]
        {G : RectMat m n | 3 * Real.exp (2 + x / r) / r < Spectral.opNorm (gram G)⁻¹} := by
      filter_upwards [gram_posDef_ae m n (by omega)] with G hG
      change (3 * Real.exp (2 + x / r) / r < Spectral.opNorm (Spectral.pinv (Matrix.of G)) ^ 2) =
        (3 * Real.exp (2 + x / r) / r < Spectral.opNorm (gram G)⁻¹)
      rw [Spectral.opNorm_pinv_sq_eq_gram_inverse_of_posDef (Matrix.of G) hG]
      rfl
    rw [measure_congr heq]
    exact inverse_gram_opNorm_tail (Nat.pos_of_ne_zero hm) hr hmr hn x

#assert_trust kernel quadratic
#assert_trust kernel quadratic_eq_dot
#assert_trust kernel quadratic_nonneg
#assert_trust kernel quadratic_abs_le
#assert_trust kernel quadratic_power_integrable
#assert_trust kernel psd_exists_eigenvalue_eq_opNorm
#assert_trust kernel gaussian_coordinate_even_moment
#assert_trust kernel gaussian_probe_lower
#assert_trust kernel odd_moment_pos
#assert_trust kernel inverse_denominator_pos
#assert_trust kernel inverse_gram_quadratic_nonneg
#assert_trust kernel inverse_gram_opNorm_measurable
#assert_trust kernel directionalQuadratic_joint_measurable
#assert_trust kernel inverse_gram_opNorm_moment
#assert_trust kernel odd_moment_ge_factorial
#assert_trust kernel radial_moment_le
#assert_trust kernel inverse_denominator_ge_odd
#assert_trust kernel inverse_gram_opNorm_moment_bound
#assert_trust kernel inverse_gram_opNorm_tail
#assert_trust kernel gaussian_pinv_tail
#print axioms inverse_gram_opNorm_moment
#print axioms gaussian_pinv_tail
end NLA.IE06.GaussianOperatorInverse
