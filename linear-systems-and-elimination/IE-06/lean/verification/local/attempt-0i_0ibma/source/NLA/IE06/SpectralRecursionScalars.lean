/-
Exact numerical bounds for spectral recursion, independently reviewed before
implementation in reviews/spectral-recursion-specification.md.
-/
import NLA.IE06.ScalarRecurrence

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.IE06.SpectralRecursionScalars
open ScalarRecurrence

theorem cost_nonneg {ℓ : ℝ} (hℓ : 0≤ℓ) (n d : ℕ) : 0≤cost n ℓ d := by
  unfold cost
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> positivity

theorem cost_ge_first {n d : ℕ} {ℓ : ℝ} (hℓ : 0≤ℓ) (hd : 0<d) (hdn : d<n) :
    1+ℓ/d≤cost n ℓ d := by
  rw [cost_recurrence ℓ hd hdn]
  exact le_add_of_nonneg_right (cost_nonneg hℓ _ _)

theorem profile_le_linear {n d : ℕ} {ℓ D : ℝ} (hℓ : 0≤ℓ) (hD : 0≤D) :
    profile n ℓ D d≤(d:ℝ)/Real.sqrt n := by
  unfold profile
  have he : Real.exp (-D*cost n ℓ d)≤1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hD) (cost_nonneg hℓ n d))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he
    (div_nonneg (Nat.cast_nonneg d) (Real.sqrt_nonneg _))

theorem profile_lt_sqrt {n d : ℕ} {ℓ D : ℝ} (hd : 0<d) (hdn : d<n)
    (hℓ : 0≤ℓ) (hD : 0≤D) : profile n ℓ D d<Real.sqrt d := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hnR : (0:ℝ)<n := by exact_mod_cast lt_trans hd hdn
  apply (profile_le_linear hℓ hD).trans_lt
  apply (div_lt_iff₀ (Real.sqrt_pos.mpr hnR)).mpr
  have hs : Real.sqrt (d:ℝ)<Real.sqrt n := Real.sqrt_lt_sqrt hdR.le (by exact_mod_cast hdn)
  have hm := mul_lt_mul_of_pos_left hs (Real.sqrt_pos.mpr hdR)
  simpa only [← pow_two, Real.sq_sqrt hdR.le] using hm

def baseTheta (ℓ D : ℝ) (d : ℕ) : ℝ := Real.exp (-(D-4)*(1+ℓ/d))

theorem baseTheta_pos (ℓ D : ℝ) (d : ℕ) : 0<baseTheta ℓ D d := Real.exp_pos _

theorem baseTheta_le_one {ℓ D : ℝ} (hℓ : 0≤ℓ) (hD : 4≤D) (d : ℕ) :
    baseTheta ℓ D d≤1 := by
  apply Real.exp_le_one_iff.mpr
  have : 0≤(D-4)*(1+ℓ/(d:ℝ)) := by positivity
  linarith

theorem four_exp_one_le_exp_four : 4*Real.exp 1≤Real.exp 4 := by
  have h : (4:ℝ)≤Real.exp 3 := by
    have he := Real.add_one_le_exp (3:ℝ)
    norm_num at he ⊢
    exact he
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_nonneg 1)
  calc
    _ ≤ Real.exp 3*Real.exp 1 := hm
    _ = Real.exp 4 := by rw [← Real.exp_add]; norm_num

theorem profile_le_base_threshold {n t d : ℕ} (_hn : 0<n) (hd : 0<d)
    (hdt : d<t) (htn : t≤n) {ℓ D : ℝ} (hℓ : 0≤ℓ) (hD : 4≤D) :
    profile n ℓ D d ≤ (d:ℝ)*baseTheta ℓ D d/(4*Real.exp 1*Real.sqrt t) := by
  have hDn : 0≤D := by linarith
  have hu : 1≤1+ℓ/(d:ℝ) := le_add_of_nonneg_right (by positivity)
  have hc := cost_ge_first hℓ hd (lt_of_lt_of_le hdt htn)
  have hcost : Real.exp (-D*cost n ℓ d) ≤
      Real.exp (-(D-4)*(1+ℓ/d))*Real.exp (-4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hc hDn
    nlinarith only [hm,hu]
  have he4 : Real.exp (-4)≤(4*Real.exp 1)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by positivity) four_exp_one_le_exp_four
  have hscale : (d:ℝ)/Real.sqrt n ≤ (d:ℝ)/Real.sqrt t := by
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg d)
      (Real.sqrt_pos.mpr (by exact_mod_cast lt_trans hd hdt))
      (Real.sqrt_le_sqrt (by exact_mod_cast htn))
  have htheta0 : 0≤baseTheta ℓ D d := (baseTheta_pos _ _ _).le
  unfold profile
  calc
    _ ≤ ((d:ℝ)/Real.sqrt t)*(baseTheta ℓ D d*Real.exp (-4)) :=
      mul_le_mul hscale hcost (Real.exp_nonneg _) (by positivity)
    _ ≤ ((d:ℝ)/Real.sqrt t)*(baseTheta ℓ D d*(4*Real.exp 1)⁻¹) := by
      gcongr
    _ = _ := by ring

theorem base_step_dimension {t d : ℕ} {ℓ : ℝ} (hℓ : 0<ℓ) (hd : 0<d)
    (ht : t≤8*step ℓ d) : (t:ℝ)*ℓ≤8*(d:ℝ)^2+800*d*ℓ := by
  have htR : (t:ℝ)≤8*(step ℓ d:ℝ) := by exact_mod_cast ht
  have hs := step_cast_upper hℓ hd
  calc
    _ ≤ (8*(step ℓ d:ℝ))*ℓ := mul_le_mul_of_nonneg_right htR hℓ.le
    _ ≤ (8*((d:ℝ)^2/ℓ+100*d))*ℓ := by gcongr
    _ = _ := by field_simp; ring

theorem base_exponent_bound {t d : ℕ} {ℓ β D : ℝ}
    (hℓ : 0≤ℓ) (hd : 0<d) (hβ : 1≤β) (hD : 4*β+4004≤D)
    (ht : (t:ℝ)*ℓ≤8*(d:ℝ)^2+800*d*ℓ) :
    ((t:ℝ)+d+1)*ℓ-(D-4)*(1+ℓ/d)*((d:ℝ)^2/4)≤-β*ℓ := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  have hfirst : ((d:ℝ)+1+β)*ℓ≤(β+2)*d*ℓ := by
    have h : 0≤(β+1)*((d:ℝ)-1) := mul_nonneg (by linarith) (by linarith)
    have hm := mul_nonneg h hℓ
    nlinarith only [hm]
  have hweight : 0≤((d:ℝ)^2+d*ℓ)/4 := by positivity
  have hm := mul_le_mul_of_nonneg_right hD hweight
  have he : (1+ℓ/(d:ℝ))*((d:ℝ)^2/4)=((d:ℝ)^2+d*ℓ)/4 := by field_simp
  rw [mul_assoc,he]
  have hs : 0≤(β+992)*(d:ℝ)^2 := by positivity
  have hdl : 0≤(d:ℝ)*ℓ := by positivity
  nlinarith only [hm,hfirst,ht,hs,hdl]

theorem base_union_bound {n t d : ℕ} (hn : 0<n) (_hdt : d<t) (htn : t≤n)
    (hd : 0<d) {β D : ℝ} (hβ : 1≤β) (hD : 4*β+4004≤D)
    (hlog : 0<Real.log (n:ℝ)) (ht : t≤8*step (Real.log (n:ℝ)) d) :
    (n:ℝ)^t*(t:ℝ)^(d+1)*(baseTheta (Real.log (n:ℝ)) D d)^((d:ℝ)^2/4) ≤
      Real.exp (-β*Real.log (n:ℝ)) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have htpow : (t:ℝ)^(d+1)≤(n:ℝ)^(d+1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg t) (by exact_mod_cast htn) _
  have hnexp (a : ℕ) : (n:ℝ)^a=Real.exp ((a:ℝ)*Real.log n) := by
    rw [Real.exp_nat_mul,Real.exp_log hnR]
  have htheta : (baseTheta (Real.log (n:ℝ)) D d)^((d:ℝ)^2/4)=
      Real.exp (-(D-4)*(1+Real.log (n:ℝ)/d)*((d:ℝ)^2/4)) := by
    rw [Real.rpow_def_of_pos (baseTheta_pos _ _ _)]
    simp only [baseTheta,Real.log_exp]
  have htheta0 : 0≤(baseTheta (Real.log (n:ℝ)) D d)^((d:ℝ)^2/4) :=
    Real.rpow_nonneg (baseTheta_pos _ _ _).le _
  calc
    _ ≤ (n:ℝ)^t*(n:ℝ)^(d+1)*(baseTheta (Real.log (n:ℝ)) D d)^((d:ℝ)^2/4) := by gcongr
    _ = Real.exp (((t:ℝ)+d+1)*Real.log (n:ℝ)-
        (D-4)*(1+Real.log (n:ℝ)/d)*((d:ℝ)^2/4)) := by
      rw [hnexp,hnexp,htheta,← Real.exp_add,← Real.exp_add]
      congr 1
      push_cast
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (base_exponent_bound hlog.le hd hβ hD
      (base_step_dimension hlog hd ht))

theorem profile_recurrence_le {n d : ℕ} (hn : 0<n) (hd : 0<d) (hdn : d<n)
    {ℓ C D : ℝ} (hℓ : 0<ℓ) (hC : 0≤C) (hD : 100*C≤D) :
    profile n ℓ D d ≤ (profile n ℓ D (step ℓ d)*(d:ℝ)/(step ℓ d:ℝ))*
      Real.exp (-C*(1+(step ℓ d:ℝ)*ℓ/(d:ℝ)^2)) := by
  have hstep := step_loss_le hℓ hd
  have hc := mul_le_mul_of_nonneg_left hstep hC
  have hu : 0≤1+ℓ/(d:ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_right hD hu
  have hexp : Real.exp (-D*(1+ℓ/(d:ℝ)))≤
      Real.exp (-C*(1+(step ℓ d:ℝ)*ℓ/(d:ℝ)^2)) := by
    apply Real.exp_le_exp.mpr
    simp only [div_eq_mul_inv] at hc hm ⊢
    nlinarith only [hc,hm,hC]
  have hg0 : 0≤profile n ℓ D (step ℓ d) := (profile_pos hn (step_pos ℓ hd) ℓ D).le
  rw [profile_recurrence hn hd hdn]
  calc
    _ ≤ ((d:ℝ)/(step ℓ d:ℝ))*
        Real.exp (-C*(1+(step ℓ d:ℝ)*ℓ/(d:ℝ)^2))*profile n ℓ D (step ℓ d) := by
      gcongr
    _ = _ := by ring

theorem sixteen_le_ceil_sqrt {ℓ : ℝ} (hℓ : 256≤ℓ) : 16≤⌈Real.sqrt ℓ⌉₊ := by
  have hs : (16:ℝ)≤Real.sqrt ℓ := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by norm_num; exact hℓ)
  have h := hs.trans (Nat.le_ceil _)
  exact_mod_cast h

#assert_trust kernel cost_nonneg
#print axioms cost_nonneg
#assert_trust kernel cost_ge_first
#print axioms cost_ge_first
#assert_trust kernel profile_le_linear
#print axioms profile_le_linear
#assert_trust kernel profile_lt_sqrt
#print axioms profile_lt_sqrt
#assert_trust kernel baseTheta
#print axioms baseTheta
#assert_trust kernel baseTheta_pos
#print axioms baseTheta_pos
#assert_trust kernel baseTheta_le_one
#print axioms baseTheta_le_one
#assert_trust kernel four_exp_one_le_exp_four
#print axioms four_exp_one_le_exp_four
#assert_trust kernel profile_le_base_threshold
#print axioms profile_le_base_threshold
#assert_trust kernel base_step_dimension
#print axioms base_step_dimension
#assert_trust kernel base_exponent_bound
#print axioms base_exponent_bound
#assert_trust kernel base_union_bound
#print axioms base_union_bound
#assert_trust kernel profile_recurrence_le
#print axioms profile_recurrence_le
#assert_trust kernel sixteen_le_ceil_sqrt
#print axioms sixteen_le_ceil_sqrt
end NLA.IE06.SpectralRecursionScalars
