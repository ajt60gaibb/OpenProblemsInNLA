import Mathlib
import LeanCert.Tactic.Verification

/-! Symbolic absorption of the exact all-stage smoothing threshold.
The real and eventual contracts were independently approved before code. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Filter
namespace NLA.IE06.FinalGrowthScalars

def cap (r : ℕ) (x τ : ℝ) : ℝ :=
  (2:ℝ)^(5*r)*Real.sqrt (1+(2+4*x)*τ)*
    (1+Real.sqrt (8*(r:ℝ)+4*x)*Real.sqrt (3*Real.exp (2+x/r)/r))

def coefficient (a : ℝ) : ℝ :=
  Real.exp 1 * Real.sqrt (2*a) * Real.sqrt (1+12*a) * (1+Real.sqrt (60*a))

def constant (D a : ℝ) : ℝ := 20+6*D+a+coefficient a

theorem constant_pos {D a : ℝ} (hD : 0≤D) (ha : 1≤a) : 0<constant D a := by
  have hB : 0≤coefficient a := by unfold coefficient; positivity
  unfold constant
  linarith

theorem ceil_bounds {y : ℝ} (hy : 1≤y) :
    y≤(⌈y⌉₊:ℝ) ∧ (⌈y⌉₊:ℝ)≤2*y :=
  ⟨Nat.le_ceil y, (Nat.ceil_lt_add_one (by linarith : 0≤y)).le.trans (by linarith)⟩

theorem exp_sq (z : ℝ) : (Real.exp z)^2 = Real.exp (2*z) := by
  rw [pow_two,← Real.exp_add]
  congr 1
  ring

theorem first_factor_le {N y D a : ℝ} {r : ℕ}
    (hN : 1≤N) (hy : 1≤y) (hD : 0≤D) (ha : 1≤a) (hyr : y≤(r:ℝ)) :
    Real.sqrt (1+(2+4*(a*y^2))*((2*N/r)*Real.exp (12*D*y))) ≤
      Real.sqrt (1+12*a)*Real.sqrt N*y*Real.exp (6*D*y) := by
  have hr : (1:ℝ)≤r := hy.trans hyr
  have hy0 : 0≤y := by linarith
  have hN0 : 0≤N := by linarith
  have ha0 : 0≤a := by linarith
  have he : 1≤Real.exp (12*D*y) := Real.one_le_exp_iff.mpr (by positivity)
  have ht : (2*N/r)*Real.exp (12*D*y) ≤ 2*N*Real.exp (12*D*y) := by
    gcongr
    exact div_le_self (by positivity) hr
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hN0,exp_sq]
  have hexp : 2*(6*D*y)=12*D*y := by ring
  rw [hexp]
  have hcoef : 2+4*(a*y^2) ≤ 6*a*y^2 := by nlinarith [sq_nonneg (y-1)]
  have hmul := mul_le_mul ht hcoef (by positivity : 0≤2+4*(a*y^2)) (by positivity : 0≤2*N*Real.exp (12*D*y))
  have hunit : 1≤N*y^2*Real.exp (12*D*y) := by
    have hy2 : 1≤y^2 := by nlinarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN hy2) he
  nlinarith

theorem smoothing_factor_le {y a : ℝ} {r : ℕ}
    (hy : 1≤y) (ha : 1≤a) (hyr : y≤(r:ℝ)) (hry : (r:ℝ)≤2*y) :
    1+Real.sqrt (8*(r:ℝ)+4*(a*y^2))*Real.sqrt (3*Real.exp (2+(a*y^2)/r)/r) ≤
      (1+Real.sqrt (60*a))*y*Real.exp (1+a*y/2) := by
  have hy0 : 0≤y := by linarith
  have hr : (1:ℝ)≤r := hy.trans hyr
  have hr0 : (0:ℝ)<r := by linarith
  have ha0 : 0≤a := by linarith
  have hq : a*y^2/(r:ℝ) ≤ a*y := (div_le_iff₀ hr0).mpr (by
    have h := mul_le_mul_of_nonneg_left hyr (mul_nonneg ha0 hy0)
    nlinarith)
  have hs1 : Real.sqrt (8*(r:ℝ)+4*(a*y^2)) ≤ Real.sqrt (20*a)*y := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg (y-1)]
  have hs2 : Real.sqrt (3*Real.exp (2+(a*y^2)/r)/r) ≤
      Real.sqrt 3*Real.exp (1+a*y/2) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,Real.sq_sqrt (by norm_num),exp_sq]
    calc
      _ ≤ 3*Real.exp (2+(a*y^2)/r) := div_le_self (by positivity) hr
      _ ≤ _ := by gcongr; linarith
  have hp := mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (by positivity)
  have he : 1≤y*Real.exp (1+a*y/2) :=
    one_le_mul_of_one_le_of_one_le hy (Real.one_le_exp_iff.mpr (by positivity))
  have hsqrt : Real.sqrt (20*a)*Real.sqrt 3=Real.sqrt (60*a) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  calc
    _ ≤ 1+(Real.sqrt (20*a)*y)*(Real.sqrt 3*Real.exp (1+a*y/2)) := by linarith
    _ = 1+Real.sqrt (60*a)*y*Real.exp (1+a*y/2) := by rw [← hsqrt]; ring
    _ ≤ _ := by nlinarith

theorem two_power_le {y : ℝ} {r : ℕ} (hry : (r:ℝ)≤2*y) :
    (2:ℝ)^(5*r) ≤ Real.exp (10*y) := by
  have h2 : (2:ℝ)≤Real.exp 1 := by have h:=Real.add_one_le_exp (1:ℝ); linarith
  calc
    _ ≤ (Real.exp 1)^(5*r) := pow_le_pow_left₀ (by norm_num) h2 _
    _ = Real.exp ((5*r:ℕ):ℝ) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := by apply Real.exp_le_exp.mpr; push_cast; linarith

theorem cap_nonneg (r : ℕ) (x τ : ℝ) : 0≤cap r x τ := by
  unfold cap
  positivity

/-- Stronger uniform real form, with no relation required between N and y. -/
theorem real_absorption {N y D a : ℝ} (hN : 1≤N) (hy : 1≤y)
    (hD : 0≤D) (ha : 1≤a) :
    Real.sqrt (2*(a*y^2)*(cap ⌈y⌉₊ (a*y^2)
      ((2*N/(⌈y⌉₊:ℝ))*Real.exp (12*D*y)))^2) ≤
        Real.sqrt N*Real.exp (constant D a*y) := by
  have hy0 : 0≤y := by linarith
  have ha0 : 0≤a := by linarith
  have hN0 : 0≤N := by linarith
  obtain ⟨hyr,hry⟩ := ceil_bounds hy
  let r := ⌈y⌉₊
  let K := cap r (a*y^2) ((2*N/r)*Real.exp (12*D*y))
  have hK0 : 0≤K := cap_nonneg _ _ _
  have hK : K ≤ Real.exp (10*y)*
      (Real.sqrt (1+12*a)*Real.sqrt N*y*Real.exp (6*D*y))*
      ((1+Real.sqrt (60*a))*y*Real.exp (1+a*y/2)) := by
    dsimp only [K,cap]
    exact mul_le_mul
      (mul_le_mul (two_power_le hry) (first_factor_le hN hy hD ha hyr)
        (Real.sqrt_nonneg _) (Real.exp_nonneg _))
      (smoothing_factor_le hy ha hyr hry)
      (by positivity) (by positivity)
  have hrad : Real.sqrt (2*(a*y^2)*K^2) = Real.sqrt (2*a)*y*K := by
    have he : 2*(a*y^2)*K^2 = (2*a)*(y*K)^2 := by ring
    rw [he,Real.sqrt_mul (by positivity),Real.sqrt_sq (mul_nonneg hy0 hK0)]
    ring
  have hraw : Real.sqrt (2*(a*y^2)*K^2) ≤
      Real.sqrt N*(coefficient a*y^3*Real.exp ((10+6*D+a/2)*y)) := by
    rw [hrad]
    apply (mul_le_mul_of_nonneg_left hK (by positivity : 0≤Real.sqrt (2*a)*y)).trans_eq
    have he : Real.exp (10*y)*Real.exp (6*D*y)*Real.exp (1+a*y/2) =
        Real.exp 1*Real.exp ((10+6*D+a/2)*y) := by
      rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    calc
      _ = (Real.sqrt (2*a)*Real.sqrt (1+12*a)*(1+Real.sqrt (60*a)))*
          Real.sqrt N*y^3*(Real.exp (10*y)*Real.exp (6*D*y)*Real.exp (1+a*y/2)) := by ring
      _ = _ := by rw [he]; unfold coefficient; ring
  have hB0 : 0≤coefficient a := by unfold coefficient; positivity
  have hB : coefficient a ≤ Real.exp (coefficient a*y) := by
    apply (show coefficient a ≤ Real.exp (coefficient a) by
      have h:=Real.add_one_le_exp (coefficient a); linarith).trans
    apply Real.exp_le_exp.mpr
    nlinarith
  have hyexp : y≤Real.exp y := by have h:=Real.add_one_le_exp y; linarith
  have hypow : y^3≤Real.exp (3*y) := by
    calc
      y^3 ≤ (Real.exp y)^3 := pow_le_pow_left₀ hy0 hyexp _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hfinal : coefficient a*y^3*Real.exp ((10+6*D+a/2)*y) ≤
      Real.exp (constant D a*y) := by
    calc
      _ ≤ Real.exp (coefficient a*y)*Real.exp (3*y)*Real.exp ((10+6*D+a/2)*y) := by
        gcongr
      _ = Real.exp ((coefficient a+3+(10+6*D+a/2))*y) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        unfold constant
        nlinarith
  exact hraw.trans (mul_le_mul_of_nonneg_left hfinal (Real.sqrt_nonneg _))

/-- Natural-dimension specialization with the literal log-based parameters. -/
theorem log_absorption {D a : ℝ} (hD : 0≤D) (ha : 1≤a) {n : ℕ}
    (hn : 1≤Real.log (n:ℝ)) :
    Real.sqrt (2*(a*Real.log n)*(cap ⌈Real.sqrt (Real.log n)⌉₊ (a*Real.log n)
      ((2*(n:ℝ)/(⌈Real.sqrt (Real.log n)⌉₊:ℝ))*Real.exp (12*D*Real.sqrt (Real.log n))))^2) ≤
        Real.sqrt n*Real.exp (constant D a*Real.sqrt (Real.log n)) := by
  have hnpos : (0:ℝ)<n := by
    by_contra h
    have hz : n=0 := by exact_mod_cast (le_antisymm (not_lt.mp h) (Nat.cast_nonneg n))
    simp [hz] at hn
    linarith
  have hN : (1:ℝ)≤n := by
    have : 0<n := by exact_mod_cast hnpos
    exact_mod_cast this
  have hy : 1≤Real.sqrt (Real.log (n:ℝ)) :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hn)
  have h := real_absorption hN hy hD ha
  simpa only [Real.sq_sqrt (show 0≤Real.log (n:ℝ) by linarith)] using h

theorem eventual_absorption {D a : ℝ} (hD : 0≤D) (ha : 1≤a) :
    ∃ C>0, ∀ᶠ n : ℕ in atTop,
      Real.sqrt (2*(a*Real.log n)*(cap ⌈Real.sqrt (Real.log n)⌉₊ (a*Real.log n)
        ((2*(n:ℝ)/(⌈Real.sqrt (Real.log n)⌉₊:ℝ))*Real.exp (12*D*Real.sqrt (Real.log n))))^2) ≤
          Real.sqrt n*Real.exp (C*Real.sqrt (Real.log n)) := by
  refine ⟨constant D a,constant_pos hD ha,?_⟩
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop 1] with n hn
  exact log_absorption hD ha hn

#assert_trust kernel cap
#print axioms cap
#assert_trust kernel coefficient
#print axioms coefficient
#assert_trust kernel constant
#print axioms constant
#assert_trust kernel constant_pos
#print axioms constant_pos
#assert_trust kernel ceil_bounds
#print axioms ceil_bounds
#assert_trust kernel exp_sq
#print axioms exp_sq
#assert_trust kernel first_factor_le
#print axioms first_factor_le
#assert_trust kernel smoothing_factor_le
#print axioms smoothing_factor_le
#assert_trust kernel two_power_le
#print axioms two_power_le
#assert_trust kernel cap_nonneg
#print axioms cap_nonneg
#assert_trust kernel real_absorption
#print axioms real_absorption
#assert_trust kernel log_absorption
#print axioms log_absorption
#assert_trust kernel eventual_absorption
#print axioms eventual_absorption
end NLA.IE06.FinalGrowthScalars
