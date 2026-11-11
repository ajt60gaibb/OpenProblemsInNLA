import NLA.Proofs.RE06.GaussianLaplace

/-! Elementary logarithm estimates used to optimize the Gaussian bounds. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace NLA.Proofs.RE06

theorem log_one_add_ge_half (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    η / 2 ≤ Real.log (1 + η) := by
  apply le_trans _ (Real.le_log_one_add_of_nonneg hη0)
  apply (le_div_iff₀ (by linarith : 0 < η + 2)).2
  nlinarith

theorem log_one_add_ge_scaled (η x : ℝ) (hη : 0 ≤ η) (hx0 : 0 ≤ x) (hxη : x ≤ η) :
    (1 - η) * x ≤ Real.log (1 + x) := by
  have hp : 0 < 1 + x := by linarith
  have hr : x / (1 + x) ≤ Real.log (1 + x) := by
    convert Real.one_sub_inv_le_log_of_pos hp using 1
    field_simp
    ring
  refine le_trans ?_ hr
  apply (le_div_iff₀ hp).2
  have hηx := mul_nonneg hη hx0
  have hsmall : (1 - η) * x ≤ η := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsmall hx0
  nlinarith

/-- A finite convex-combination form of logarithm concavity. -/
theorem log_one_sub_mul_ge_mul_log (u a : ℝ)
    (_hu0 : 0 ≤ u) (hu1 : u < 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    a * Real.log (1 - u) ≤ Real.log (1 - u * a) := by
  have hc := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 1 - u ∈ Set.Ioi 0 by simpa using sub_pos.mpr hu1)
    (show 0 ≤ 1 - a by linarith) ha0 (show 1 - a + a = 1 by ring)
  simpa only [smul_eq_mul, Real.log_one, mul_zero, zero_add,
    show (1 - a) * 1 + a * (1 - u) = 1 - u * a by ring] using hc

/-- The upper-tail exponent has the source's quantitative constant on `[0,1]`. -/
theorem log_one_add_le_sub_quarter_sq (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    Real.log (1 + η) ≤ η - η ^ 2 / 4 := by
  let f : ℝ → ℝ := fun x => x - Real.log (1 + x) - x ^ 2 / 4
  let df : ℝ → ℝ := fun x => 1 - (1 + x)⁻¹ - x / 2
  have hd (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt f (df x) x := by
    have hp : 1 + x ≠ 0 := by linarith [hx.1]
    have hl : HasDerivAt (fun y : ℝ => Real.log (1 + y)) ((1 + x)⁻¹) x := by
      simpa only [zero_add, one_div, Pi.add_apply, id_eq] using
        (((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).log hp)
    have hs : HasDerivAt (fun y : ℝ => y ^ 2 / 4) (x / 2) x := by
      have hs0 : HasDerivAt (fun y : ℝ => y ^ 2 / 4) ((2 * x) / 4) x := by
        simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using
          (((hasDerivAt_id x).pow 2).div_const 4)
      convert hs0 using 1
      ring
    exact ((hasDerivAt_id x).sub hl).sub hs

  have hdf (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ df x := by
    have hp : 0 < 1 + x := by linarith [hx.1]
    have he : df x = x * (1 - x) / (2 * (1 + x)) := by
      dsimp [df]
      field_simp
      ring
    rw [he]
    exact div_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)) (by positivity)
  have hm : MonotoneOn f (Set.Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    · intro x hx
      exact (hd x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      exact hdf x (interior_subset hx)
  have h := hm (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num) ⟨hη0, hη1⟩ hη0
  have hz : f 0 = 0 := by simp [f]
  rw [hz] at h
  dsimp [f] at h
  linarith

#assert_trust kernel log_one_add_ge_half
#assert_trust kernel log_one_add_ge_scaled
#assert_trust kernel log_one_sub_mul_ge_mul_log
#assert_trust kernel log_one_add_le_sub_quarter_sq
#print axioms log_one_add_ge_half
#print axioms log_one_add_ge_scaled
#print axioms log_one_sub_mul_ge_mul_log
#print axioms log_one_add_le_sub_quarter_sq
end NLA.Proofs.RE06
