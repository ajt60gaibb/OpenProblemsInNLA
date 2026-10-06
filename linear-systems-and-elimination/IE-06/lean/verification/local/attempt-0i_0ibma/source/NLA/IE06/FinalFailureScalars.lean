import NLA.IE06.GaussianDenominator

/-! Symbolic final failure-probability absorption. The preimplementation
contract and root approval are in final-failure-scalars-specification.md. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace NLA.IE06.FinalFailureScalars

theorem shifted_exp_eq_div {N : ℝ} (hN : 0 < N) (α : ℝ) (j : ℕ) :
    Real.exp (-(α+j)*Real.log N)=N^(-α)/N^j := by
  have he : -(α+(j:ℝ))*Real.log N=(-α)*Real.log N-(j:ℝ)*Real.log N := by ring
  rw [he,Real.exp_sub,Real.exp_nat_mul,Real.exp_log hN,Real.rpow_def_of_pos hN]
  congr 1
  congr 1
  ring

theorem real_budget {N : ℝ} (hN : 4 ≤ N) (α : ℝ) :
    Real.exp (-((α+4)-2)*Real.log N)+(2*N^2+N+2*N^3)*Real.exp (-(α+6)*Real.log N)+
      N^(-(α+1)) < N^(-α) := by
  have hN0 : 0 < N := by linarith
  let R := N^(-α)
  have hR : 0 < R := Real.rpow_pos_of_pos hN0 _
  have htwo : Real.exp (-((α+4)-2)*Real.log N)=R/N^2 := by
    have he : (α+4)-2=α+2 := by ring
    rw [he]
    exact shifted_exp_eq_div hN0 α 2
  have hsix : Real.exp (-(α+6)*Real.log N)=R/N^6 := shifted_exp_eq_div hN0 α 6
  have hone : N^(-(α+1))=R/N := by
    have he : -(α+1)=-α-1 := by ring
    rw [he,Real.rpow_sub hN0,Real.rpow_one]
  have hN2 : 16 ≤ N^2 := by nlinarith
  have hN3 : 64 ≤ N^3 := by nlinarith [mul_le_mul hN2 hN (by norm_num : (0:ℝ)≤4) (sq_nonneg N)]
  have hpoly : 2*N^2+N+2*N^3 ≤ 5*N^3 := by
    have h1 : N ≤ N^2 := by nlinarith
    have h2 : N^2 ≤ N^3 := by nlinarith [mul_nonneg (sq_nonneg N) (by linarith : 0≤N-1)]
    linarith
  have hfirst : R/N^2 ≤ R/16 := div_le_div_of_nonneg_left hR.le (by norm_num) hN2
  have hthird : R/N ≤ R/4 := div_le_div_of_nonneg_left hR.le (by norm_num) hN
  have hsecond : (2*N^2+N+2*N^3)*(R/N^6) ≤ 5*R/64 := by
    calc
      _ ≤ 5*N^3*(R/N^6) := mul_le_mul_of_nonneg_right hpoly (by positivity)
      _ = 5*R/N^3 := by field_simp
      _ ≤ 5*R/64 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hN3
  rw [htwo,hsix,hone]
  change R/N^2+(2*N^2+N+2*N^3)*(R/N^6)+R/N < R
  linarith

/-- The actual denominator exception and all stage failure coefficients fit
strictly within the requested inverse-power budget, eventually in dimension. -/
theorem failure_budget_eventually (α : ℝ) (_hα : 0 < α) :
    ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-((α+4)-2)*Real.log (n:ℝ)))+
        (2*(n:ℝ≥0∞)^2+n+2*(n:ℝ≥0∞)^3)*ENNReal.ofReal (Real.exp (-(α+6)*Real.log (n:ℝ)))+
        ENNReal.ofReal (gaussianUnitIntervalMass^(n^2)) < ENNReal.ofReal ((n:ℝ)^(-α)) := by
  filter_upwards [gaussian_entryMax_lt_one_eventually (α+1),eventually_ge_atTop 4] with n hq hn
  rw [gaussian_entryMax_lt_one_probability] at hq
  have hnr : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have hfinite : ENNReal.ofReal (Real.exp (-((α+4)-2)*Real.log (n:ℝ)))+
      (2*(n:ℝ≥0∞)^2+n+2*(n:ℝ≥0∞)^3)*ENNReal.ofReal (Real.exp (-(α+6)*Real.log (n:ℝ))) ≠ ⊤ := by
    finiteness
  have hless := ENNReal.add_lt_add_left hfinite hq
  have hreal := real_budget hnr α
  have hid : ENNReal.ofReal (Real.exp (-((α+4)-2)*Real.log (n:ℝ)))+
      (2*(n:ℝ≥0∞)^2+n+2*(n:ℝ≥0∞)^3)*ENNReal.ofReal (Real.exp (-(α+6)*Real.log (n:ℝ)))+
      ENNReal.ofReal ((n:ℝ)^(-(α+1))) =
      ENNReal.ofReal (Real.exp (-((α+4)-2)*Real.log (n:ℝ)))+
        ENNReal.ofReal ((2*(n:ℝ)^2+n+2*(n:ℝ)^3)*Real.exp (-(α+6)*Real.log (n:ℝ)))+
        ENNReal.ofReal ((n:ℝ)^(-(α+1))) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    have hc : ENNReal.ofReal (2*(n:ℝ)^2+n+2*(n:ℝ)^3)=
        2*(n:ℝ≥0∞)^2+n+2*(n:ℝ≥0∞)^3 := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_mul (by norm_num)]
      simp only [ENNReal.ofReal_ofNat,ENNReal.ofReal_natCast,ENNReal.ofReal_pow (Nat.cast_nonneg n)]
    rw [hc]
  rw [hid,← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at hless
  exact hless.trans ((ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hn0 _)).mpr hreal)

#assert_trust kernel shifted_exp_eq_div
#assert_trust kernel real_budget
#assert_trust kernel failure_budget_eventually
#print axioms shifted_exp_eq_div
#print axioms real_budget
#print axioms failure_budget_eventually

end NLA.IE06.FinalFailureScalars
