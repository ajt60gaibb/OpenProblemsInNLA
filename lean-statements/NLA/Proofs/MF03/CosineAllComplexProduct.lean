import Mathlib
import LeanCert.Tactic.Verification
import NLA.Proofs.MF03.CosineDenseProduct

/-! All-complex extension of the independently reviewed MF-03 cosine product. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Real Topology
open Filter

namespace NLA.Proofs.MF03

private noncomputable def cosineProductLimit (z : ℂ) : ℂ :=
  tprod (fun k : ℕ => (1 : ℂ) + (cosineFactor (k + 1) : ℂ) * z)

private theorem cosineCoefficients_summable :
    Summable (fun k : ℕ => cosineFactor (k + 1)) := by
  have hbase : Summable (fun k : ℕ =>
      1 / |(k : ℝ) + 1 / 2| ^ (2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow (1 / 2) 2).2 (by norm_num)
  have hbase' : Summable (fun k : ℕ =>
      1 / |(k : ℝ) + 1 / 2| ^ (2 : ℕ)) := by
    simpa only [Real.rpow_two] using hbase
  have hscale := hbase'.mul_left (1 / Real.pi ^ 2)
  apply hscale.congr
  intro k
  have hcast : (((k + 1 : ℕ) : ℝ) - 1 / 2) = (k : ℝ) + 1 / 2 := by
    push_cast
    ring
  have hpos : (0 : ℝ) < (k : ℝ) + 1 / 2 := by positivity
  have hfactor : cosineFactor (k + 1) =
      1 / (Real.pi ^ 2 * ((k : ℝ) + 1 / 2) ^ 2) := by
    unfold cosineFactor
    rw [hcast]
  rw [hfactor, abs_of_pos hpos, one_div_mul_one_div]

private theorem continuous_cosineProductLimit : Continuous cosineProductLimit := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  have hsum : Summable (fun k : ℕ =>
      (‖z₀‖ + 1) * cosineFactor (k + 1)) :=
    cosineCoefficients_summable.mul_left (‖z₀‖ + 1)
  have hterm (k : ℕ) : Tendsto
      (fun z : ℂ => (cosineFactor (k + 1) : ℂ) * z)
      (𝓝 z₀) (𝓝 ((cosineFactor (k + 1) : ℂ) * z₀)) := by
    exact (continuous_const.mul continuous_id).tendsto z₀
  have hlocal : ∀ᶠ z : ℂ in 𝓝 z₀, ‖z‖ < ‖z₀‖ + 1 := by
    have hlt : ‖z₀‖ < ‖z₀‖ + 1 := by linarith
    exact (continuous_norm.tendsto z₀).eventually_lt tendsto_const_nhds hlt
  have hbound : ∀ᶠ z : ℂ in 𝓝 z₀, ∀ k : ℕ,
      ‖(cosineFactor (k + 1) : ℂ) * z‖ ≤
        (‖z₀‖ + 1) * cosineFactor (k + 1) := by
    filter_upwards [hlocal] with z hz k
    have ha : 0 ≤ cosineFactor (k + 1) := by
      unfold cosineFactor
      positivity
    calc
      ‖(cosineFactor (k + 1) : ℂ) * z‖ =
          cosineFactor (k + 1) * ‖z‖ := by
        simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
      _ ≤ (‖z₀‖ + 1) * cosineFactor (k + 1) := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hz.le ha
  have h := tendsto_tprod_one_add_of_dominated_convergence
    (𝓕 := 𝓝 z₀)
    (f := fun z k => (cosineFactor (k + 1) : ℂ) * z)
    (g := fun k => (cosineFactor (k + 1) : ℂ) * z₀)
    (bound := fun k => (‖z₀‖ + 1) * cosineFactor (k + 1))
    hsum hterm hbound
  change Tendsto cosineProductLimit (𝓝 z₀) (𝓝 (cosineProductLimit z₀))
  exact h

private theorem cosinePartialProduct_tendsto_product (z : ℂ) :
    Tendsto (fun N : ℕ => cosinePartialProduct N z) atTop
      (𝓝 (cosineProductLimit z)) := by
  simpa [cosinePartialProduct, cosineProductLimit] using
    (cosineFactors_multipliable z).hasProd.tendsto_prod_nat

private theorem cosineProductLimit_eq_waveSeries_of_sin_ne_zero
    (w : ℂ) (hw : Complex.sin ((Real.pi : ℂ) * w) ≠ 0) :
    cosineProductLimit (-(((Real.pi : ℂ) * w) ^ 2)) =
      waveSeries (-(((Real.pi : ℂ) * w) ^ 2)) := by
  exact tendsto_nhds_unique
    (cosinePartialProduct_tendsto_product _)
    (cosinePartialProduct_tendsto_waveSeries_of_sin_ne_zero w hw)

private theorem sine_zero_set_eq_integer_range :
    {w : ℂ | Complex.sin ((Real.pi : ℂ) * w) = 0} =
      Set.range (fun k : ℤ => (k : ℂ)) := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have hmul : (Real.pi : ℂ) * w = (Real.pi : ℂ) * (k : ℂ) := by
      simpa [mul_comm] using hk
    exact ⟨k, (mul_left_cancel₀ hpi hmul).symm⟩
  · rintro ⟨k, rfl⟩
    apply Complex.sin_eq_zero_iff.mpr
    exact ⟨k, by ring⟩

private theorem dense_sine_nonzero :
    Dense {w : ℂ | Complex.sin ((Real.pi : ℂ) * w) ≠ 0} := by
  have hcount : (Set.range (fun k : ℤ => (k : ℂ))).Countable :=
    Set.countable_range _
  have h := hcount.dense_compl ℂ
  rw [← sine_zero_set_eq_integer_range] at h
  simpa only [Set.compl_ofPred] using h

private theorem cosineProductLimit_eq_waveSeries_quadratic (w : ℂ) :
    cosineProductLimit (-(((Real.pi : ℂ) * w) ^ 2)) =
      waveSeries (-(((Real.pi : ℂ) * w) ^ 2)) := by
  have hproduct : Continuous (fun w : ℂ =>
      cosineProductLimit (-(((Real.pi : ℂ) * w) ^ 2))) := by
    apply continuous_cosineProductLimit.comp
    fun_prop
  have hseries : Continuous (fun w : ℂ =>
      waveSeries (-(((Real.pi : ℂ) * w) ^ 2))) := by
    have hfun : (fun w : ℂ => waveSeries (-(((Real.pi : ℂ) * w) ^ 2))) =
        (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * w)) := by
      funext w
      exact waveSeries_neg_pi_sq_eq_cos w
    rw [hfun]
    fun_prop
  have hfun := Continuous.ext_on dense_sine_nonzero hproduct hseries
    (fun w hw => cosineProductLimit_eq_waveSeries_of_sin_ne_zero w hw)
  exact congrFun hfun w

private theorem quadratic_argument_surjective :
    Function.Surjective (fun w : ℂ => -(((Real.pi : ℂ) * w) ^ 2)) := by
  intro z
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (-z) (by norm_num : 0 < 2)
  refine ⟨y / (Real.pi : ℂ), ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hmul : (Real.pi : ℂ) * (y / (Real.pi : ℂ)) = y := by
    field_simp [hpi]
  dsimp
  rw [hmul, hy]
  ring

/-- The exact factorial wave series is the complete positive-factor product. -/
theorem cosineFactor_tprod_eq_waveSeries (z : ℂ) :
    tprod (fun k : ℕ => (1 : ℂ) + (cosineFactor (k + 1) : ℂ) * z) =
      waveSeries z := by
  obtain ⟨w, hw⟩ := quadratic_argument_surjective z
  rw [← hw]
  exact cosineProductLimit_eq_waveSeries_quadratic w

/-- Every finite cosine product tends to the factorial wave series value. -/
theorem cosinePartialProduct_tendsto_waveSeries (z : ℂ) :
    Tendsto (fun N : ℕ => cosinePartialProduct N z) atTop
      (𝓝 (waveSeries z)) := by
  rw [← cosineFactor_tprod_eq_waveSeries]
  exact cosinePartialProduct_tendsto_product z

#assert_trust kernel cosineFactor_tprod_eq_waveSeries
#assert_trust kernel cosinePartialProduct_tendsto_waveSeries
#print axioms cosineFactor_tprod_eq_waveSeries
#print axioms cosinePartialProduct_tendsto_waveSeries

end NLA.Proofs.MF03
