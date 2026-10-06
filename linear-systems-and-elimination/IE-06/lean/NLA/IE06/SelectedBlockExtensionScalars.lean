/-
Symbolic numerical absorption for manuscript Lemma 5.4. The exact constants
and inequalities were independently approved before implementation in
reviews/selected-block-extension-specification.md. No probability bound is
assumed in this scalar module.
-/
import NLA.IE06.GaussianAppend
import NLA.IE06.GaussianStackingTail

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.IE06.SelectedBlockExtensionScalars
open Real GaussianStackingTail

def loss (n k d : ℕ) : ℝ := (k:ℝ)*log n/(d:ℝ)^2

def thetaCoefficient (β : ℝ) : ℝ := 64*(β+6)

def theta (n k d : ℕ) (β : ℝ) : ℝ := exp (-thetaCoefficient β*(1+loss n k d))

def firstBudget (n : ℕ) (β : ℝ) : ℝ := (β+1)*log n

def candidateBudget (n k : ℕ) (β : ℝ) : ℝ := ((4*k:ℕ)+β+1)*log n

def scale (n k : ℕ) (β μ : ℝ) : ℝ :=
  sqrt GaussianAppend.appendConstant*μ⁻¹*exp (firstBudget n β/k)

def denominatorConstant : ℝ := 1+sqrt GaussianAppend.appendConstant+
  24*exp 1*(1+50*sqrt GaussianAppend.appendConstant)

def extensionConstant (β : ℝ) : ℝ :=
  thetaCoefficient β+2*β+6+log (2*denominatorConstant)+1

theorem dimensions {n m k d : ℕ} (hn : m+4*k≤ n) (hkm : k < m)
    (hd : 16≤ d) (hk : 100*d≤ k) :
    1600≤ k ∧ 5*k< n ∧ 4≤ n ∧ 8≤ d/2 ∧ 2*(d/2)≤ d ∧ d≤3*(d/2) ∧
      d≤2*(d/2+1) ∧ d/2+1≤ k ∧ 2*(d/2)<4*k ∧ d/2 < m := by omega

theorem loss_nonneg {n k d : ℕ} (hn : 1≤ n) : 0≤ loss n k d := by
  have hl : 0≤ log (n:ℝ) := log_nonneg (by exact_mod_cast hn)
  unfold loss
  positivity

theorem theta_pos (n k d : ℕ) (β : ℝ) : 0< theta n k d β := exp_pos _

theorem theta_le_one {n k d : ℕ} (hn : 1≤ n) {β : ℝ} (hβ : 1≤β) :
    theta n k d β≤1 := by
  apply exp_le_one_iff.mpr
  have hl := loss_nonneg (k:=k) (d:=d) hn
  have hC : 0≤ thetaCoefficient β := by unfold thetaCoefficient; positivity
  change -thetaCoefficient β*(1+loss n k d)≤0
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hC) (by positivity)

theorem budgets_pos {n k : ℕ} (hn : 1< n) {β : ℝ} (hβ : 1≤β) :
    0< firstBudget n β ∧ 0< candidateBudget n k β := by
  have hl : 0< log (n:ℝ) := log_pos (by exact_mod_cast hn)
  unfold firstBudget candidateBudget
  constructor <;> positivity

theorem scale_pos {n k : ℕ} (β : ℝ) {μ : ℝ} (hμ : 0<μ) : 0< scale n k β μ := by
  have hC := GaussianAppend.appendConstant_pos
  unfold scale
  positivity

theorem denominatorConstant_ge_one : 1≤ denominatorConstant := by
  have hC := GaussianAppend.appendConstant_pos
  unfold denominatorConstant
  have hs := sqrt_nonneg GaussianAppend.appendConstant
  have he := exp_pos (1:ℝ)
  nlinarith

theorem extensionConstant_pos {β : ℝ} (hβ : 1≤β) : 0< extensionConstant β := by
  have hH := denominatorConstant_ge_one
  have hl : 0≤ log (2*denominatorConstant) := log_nonneg (by linarith)
  unfold extensionConstant thetaCoefficient
  linarith

theorem candidate_exponent_bound {K d j ℓ z β : ℝ} (hℓ : 0≤ℓ) (hK : 1≤ K)
    (hβ : 1≤β) (hjk : j+1≤ K) (hz : 0≤ z) (hzprod : z*d^2=K*ℓ)
    (hdj : d^2≤16*j^2) :
    (j+1)*ℓ-64*(β+6)*(1+z)*(j^2/4)≤-(4*K+β+1)*ℓ := by
  have hB : 0≤β+6 := by linarith
  have hc := mul_le_mul_of_nonneg_left hK (by linarith : 0≤β+1)
  have hcount : j+1+4*K+β+1≤(β+6)*K := by nlinarith only [hc,hjk]
  have hcountℓ := mul_le_mul_of_nonneg_right hcount hℓ
  have hm := mul_le_mul_of_nonneg_left hdj (mul_nonneg hB hz)
  have he := congrArg (fun y : ℝ => (β+6)*y) hzprod
  have hjpos := mul_nonneg hB (sq_nonneg j)
  nlinarith only [hcountℓ,hm,he,hjpos]

theorem overcrowding_term_le {n m k d : ℕ} (hn : m+4*k≤ n) (hkm : k < m)
    (hd : 16≤ d) (hk : 100*d≤ k) {β : ℝ} (hβ : 1≤β) :
    ((4*k:ℕ):ℝ)^(d/2+1)*(theta n k d β)^(((d/2:ℕ):ℝ)^2/4)≤
      exp (-candidateBudget n k β) := by
  obtain ⟨hk1600,h5n,hn4,hj8,h2j,hdj,hdj1,hj1k,h2js,hjm⟩ := dimensions hn hkm hd hk
  have hk0 : 0< k := by omega
  have hd0 : 0< d := by omega
  have hn1 : 1< n := by omega
  have hℓ : 0≤ log (n:ℝ) := (log_pos (by exact_mod_cast hn1)).le
  have hz : 0≤ loss n k d := loss_nonneg (by omega)
  have hzprod : loss n k d*(d:ℝ)^2=(k:ℝ)*log n := by
    unfold loss
    exact div_mul_cancel₀ _ (pow_ne_zero _ (by exact_mod_cast hd0.ne'))
  have hdjR : (d:ℝ)≤3*(d/2:ℕ) := by exact_mod_cast hdj
  have hdsq : (d:ℝ)^2≤16*((d/2:ℕ):ℝ)^2 := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg d) hdjR 2
    nlinarith only [hh,sq_nonneg ((d/2:ℕ):ℝ)]
  have hexp := candidate_exponent_bound hℓ (by exact_mod_cast (show 1≤ k by omega)) hβ
    (by exact_mod_cast hj1k) hz hzprod hdsq
  have hlog : log ((4*k:ℕ):ℝ)≤ log (n:ℝ) :=
    log_le_log (by exact_mod_cast (show 0<4*k by omega)) (by exact_mod_cast (show 4*k≤ n by omega))
  have hlogmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0≤((d/2:ℕ):ℝ)+1)
  have hpow : ((4*k:ℕ):ℝ)^(d/2+1)=
      exp ((((d/2:ℕ):ℝ)+1)*log ((4*k:ℕ):ℝ)) := by
    simp only [← Nat.cast_add_one]
    rw [exp_nat_mul,exp_log (by exact_mod_cast (show 0<4*k by omega))]
  rw [hpow,Real.rpow_def_of_pos (theta_pos _ _ _ _)]
  simp only [theta,log_exp]
  rw [← exp_add]
  apply exp_le_exp.mpr
  dsimp only [thetaCoefficient,candidateBudget]
  push_cast at hlogmul ⊢
  nlinarith only [hexp,hlogmul]

theorem probability_accounting {n k : ℕ} (hn : 4≤ n) (β : ℝ) :
    2*exp (-firstBudget n β)+2*(n:ℝ)^(4*k)*exp (-candidateBudget n k β)≤
      exp (-β*log (n:ℝ)) := by
  have hnR : (0:ℝ)< n := by exact_mod_cast (show 0< n by omega)
  have hpow : (n:ℝ)^(4*k)=exp (((4*k:ℕ):ℝ)*log n) := by
    rw [exp_nat_mul,exp_log hnR]
  have he : (n:ℝ)^(4*k)*exp (-candidateBudget n k β)=exp (-firstBudget n β) := by
    rw [hpow,← exp_add]
    congr 1
    unfold candidateBudget firstBudget
    ring
  calc
    _ = 4*exp (-firstBudget n β) := by rw [show 2*(n:ℝ)^(4*k)*exp (-candidateBudget n k β)=
        2*((n:ℝ)^(4*k)*exp (-candidateBudget n k β)) by ring,he]; ring
    _ ≤ (n:ℝ)*exp (-firstBudget n β) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (exp_nonneg _)
    _ = _ := by
      rw [← exp_log hnR,← exp_add]
      congr 1
      unfold firstBudget
      simp only [log_exp]
      ring


theorem loss_comparisons {n k d : ℕ} (hn : 1≤ n) (hd : 0< d) (hdk : d≤ k) :
    log (n:ℝ)/(k:ℝ)≤ loss n k d ∧ log (n:ℝ)≤(d:ℝ)*loss n k d := by
  have hdR : (0:ℝ)< d := by exact_mod_cast hd
  have hkR : (0:ℝ)< k := by exact_mod_cast (show 0< k by omega)
  have hdkR : (d:ℝ)≤ k := by exact_mod_cast hdk
  have hℓ : 0≤ log (n:ℝ) := log_nonneg (by exact_mod_cast hn)
  have hsq : (d:ℝ)^2≤(k:ℝ)^2 := pow_le_pow_left₀ hdR.le hdkR 2
  constructor
  · unfold loss
    apply (div_le_div_iff₀ hkR (sq_pos_of_pos hdR)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hsq hℓ]
  · unfold loss
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos hdR)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hdkR (mul_nonneg hdR.le hℓ)]

theorem candidate_root_le {K d j ℓ z β : ℝ} (hK : 1≤ K) (_hd : 0< d)
    (hj : 0< j+1) (hβ : 1≤β) (hℓ : 0≤ℓ) (hz : 0≤ z)
    (hdj : d≤2*(j+1)) (hℓd : ℓ≤ d*z) :
    sqrt (2*((4*K+β+1)*ℓ)/(j+1))≤2*sqrt K*sqrt ((β+5)*z) := by
  have hB : 0≤β+5 := by linarith
  have hc : 4*K+β+1≤(β+5)*K := by
    have hh := mul_le_mul_of_nonneg_left hK (by linarith : 0≤β+1)
    nlinarith only [hh]
  have h1 := mul_le_mul_of_nonneg_right hc hℓ
  have h2 := mul_le_mul_of_nonneg_left hℓd (mul_nonneg hB (by linarith : 0≤ K))
  have h3 := mul_le_mul_of_nonneg_right hdj
    (mul_nonneg (mul_nonneg hB (by linarith : 0≤ K)) hz)
  have hrad : 2*((4*K+β+1)*ℓ)/(j+1)≤4*K*((β+5)*z) := by
    apply (div_le_iff₀ hj).mpr
    nlinarith only [h1,h2,h3]
  have hnon : 0≤2*((4*K+β+1)*ℓ)/(j+1) := by positivity
  apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
  rw [sq_sqrt hnon]
  have hKs := sq_sqrt (by linarith : 0≤ K)
  have hBs := sq_sqrt (mul_nonneg hB hz)
  nlinarith only [hrad,hKs,hBs]

theorem two_sqrt_le_exp {r : ℝ} (hr : 0≤ r) : 2*sqrt r≤ exp r := by
  have hs := sq_sqrt hr
  have hsq := sq_nonneg (sqrt r-1)
  have he := add_one_le_exp r
  nlinarith only [hs,hsq,he]

theorem product_threshold_le {n m k d : ℕ} (hn : m+4*k≤ n) (hkm : k < m)
    (hd : 16≤ d) (hk : 100*d≤ k) {β μ : ℝ} (hβ : 1≤β) (hμ : 0<μ) :
    productThreshold (4*k) (d/2) (scale n k β μ) (sqrt k*scale n k β μ)
      (candidateBudget n k β) ≤
      50*sqrt GaussianAppend.appendConstant*(sqrt k/μ)*
        exp ((2*β+6)*loss n k d) := by
  obtain ⟨hk1600,h5n,hn4,hj8,h2j,hdj,hdj1,hj1k,h2js,hjm⟩ := dimensions hn hkm hd hk
  have hk0 : 0< k := by omega
  have hd0 : 0< d := by omega
  have hz := loss_nonneg (k:=k) (d:=d) (show 1≤ n by omega)
  have hℓ : 0≤ log (n:ℝ) := log_nonneg (by exact_mod_cast (show 1≤ n by omega))
  have hcomp := loss_comparisons (show 1≤ n by omega) hd0 (show d≤ k by omega)
  have hroot := candidate_root_le (K:=(k:ℝ)) (d:=(d:ℝ)) (j:=((d/2:ℕ):ℝ))
    (by exact_mod_cast (show 1≤ k by omega)) (by exact_mod_cast hd0)
    (by positivity) hβ hℓ hz (by exact_mod_cast hdj1) hcomp.2
  have hs4 : sqrt ((4*k:ℕ):ℝ)=2*sqrt (k:ℝ) := by
    push_cast
    rw [sqrt_mul (by norm_num : (0:ℝ)≤4)]
    norm_num
  have hscale := (scale_pos (n:=n) (k:=k) β hμ).le
  have hraw : productThreshold (4*k) (d/2) (scale n k β μ)
      (sqrt k*scale n k β μ) (candidateBudget n k β) ≤
      sqrt k*scale n k β μ*(48+2*sqrt ((β+5)*loss n k d)) := by
    unfold productThreshold candidateBudget
    push_cast
    push_cast at hs4
    rw [hs4]
    have hh := mul_le_mul_of_nonneg_right hroot hscale
    nlinarith only [hh]
  have hr : 0≤(β+5)*loss n k d := mul_nonneg (by linarith) hz
  have he : 1≤ exp ((β+5)*loss n k d) := one_le_exp hr
  have hcoef : 48+2*sqrt ((β+5)*loss n k d)≤50*exp ((β+5)*loss n k d) := by
    linarith [two_sqrt_le_exp hr]
  have haExp : firstBudget n β/(k:ℝ)≤(β+1)*loss n k d := by
    unfold firstBudget
    calc
      _ = (β+1)*(log (n:ℝ)/(k:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcomp.1 (by linarith)
  have ha : scale n k β μ≤ sqrt GaussianAppend.appendConstant*μ⁻¹*
      exp ((β+1)*loss n k d) := by
    unfold scale
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr haExp) (by positivity)
  calc
    _ ≤ sqrt k*scale n k β μ*(50*exp ((β+5)*loss n k d)) :=
      hraw.trans (mul_le_mul_of_nonneg_left hcoef (by positivity))
    _ ≤ sqrt k*(sqrt GaussianAppend.appendConstant*μ⁻¹*exp ((β+1)*loss n k d))*
        (50*exp ((β+5)*loss n k d)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha (sqrt_nonneg _)) (by positivity)
    _ = _ := by
      rw [show (2*β+6)*loss n k d=(β+1)*loss n k d+(β+5)*loss n k d by ring,exp_add]
      simp only [div_eq_mul_inv]
      ring


theorem compression_pos {k d : ℕ} (hk : 0< k) (hd : 2≤ d) {θ : ℝ}
    (hθ : 0<θ) : 0< compressionThreshold (4*k) (d/2) θ := by
  have hj : 0< d/2 := by omega
  unfold compressionThreshold
  positivity

theorem compression_inverse_le {n m k d : ℕ} (hn : m+4*k≤ n) (hkm : k < m)
    (hd : 16≤ d) (hk : 100*d≤ k) (β : ℝ) :
    (compressionThreshold (4*k) (d/2) (theta n k d β))⁻¹ ≤
      24*exp 1*sqrt k/(d:ℝ)*exp (thetaCoefficient β*(1+loss n k d)) := by
  obtain ⟨hk1600,h5n,hn4,hj8,h2j,hdj,hdj1,hj1k,h2js,hjm⟩ := dimensions hn hkm hd hk
  have hjR : (0:ℝ)<(d/2:ℕ) := by exact_mod_cast (show 0< d/2 by omega)
  have hdR : (0:ℝ)< d := by exact_mod_cast (show 0< d by omega)
  have htInv : (theta n k d β)⁻¹=exp (thetaCoefficient β*(1+loss n k d)) := by
    unfold theta
    rw [← exp_neg]
    congr 1
    ring
  have hs4 : sqrt ((4*k:ℕ):ℝ)=2*sqrt (k:ℝ) := by
    push_cast
    rw [sqrt_mul (by norm_num : (0:ℝ)≤4)]
    norm_num
  have hi : (compressionThreshold (4*k) (d/2) (theta n k d β))⁻¹=
      (8*exp 1*sqrt k/((d/2:ℕ):ℝ))*exp (thetaCoefficient β*(1+loss n k d)) := by
    unfold compressionThreshold
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,hs4,htInv]
    ring
  rw [hi]
  apply mul_le_mul_of_nonneg_right _ (exp_nonneg _)
  apply (div_le_div_iff₀ hjR hdR).mpr
  have hdjR : (d:ℝ)≤3*((d/2:ℕ):ℝ) := by exact_mod_cast hdj
  have hh := mul_le_mul_of_nonneg_left hdjR (by positivity : 0≤8*exp 1*sqrt (k:ℝ))
  nlinarith only [hh]

theorem stacking_denominator_le {n m k d : ℕ} (hn : m+4*k≤ n) (hkm : k < m)
    (hd : 16≤ d) (hk : 100*d≤ k) {β μ : ℝ} (hβ : 1≤β) (hμ : 0<μ)
    (hμk : μ≤ sqrt k) :
    scale n k β μ +
      (1+productThreshold (4*k) (d/2) (scale n k β μ) (sqrt k*scale n k β μ)
        (candidateBudget n k β))/compressionThreshold (4*k) (d/2) (theta n k d β) ≤
      denominatorConstant*((k:ℝ)/(μ*d))*
        exp ((thetaCoefficient β+2*β+6)*(1+loss n k d)) := by
  obtain ⟨hk1600,h5n,hn4,hj8,h2j,hdj,hdj1,hj1k,h2js,hjm⟩ := dimensions hn hkm hd hk
  have hkR : (0:ℝ)< k := by exact_mod_cast (show 0< k by omega)
  have hdR : (0:ℝ)< d := by exact_mod_cast (show 0< d by omega)
  have hdk : (d:ℝ)≤ k := by exact_mod_cast (show d≤ k by omega)
  have hz := loss_nonneg (k:=k) (d:=d) (show 1≤ n by omega)
  have hcomp := loss_comparisons (show 1≤ n by omega) (show 0< d by omega) (show d≤ k by omega)
  have hD : 0≤ thetaCoefficient β := by unfold thetaCoefficient; linarith
  have hE : 0≤2*β+6 := by linarith
  have hH := denominatorConstant_ge_one
  have hspos := sqrt_pos.mpr hkR
  have hsRatio : 1≤ sqrt (k:ℝ)/μ := (le_div_iff₀ hμ).mpr (by simpa using hμk)
  have hExpE : 1≤ exp ((2*β+6)*loss n k d) := one_le_exp (mul_nonneg hE hz)
  have hunit : 1≤ sqrt (k:ℝ)/μ*exp ((2*β+6)*loss n k d) :=
    one_le_mul_of_one_le_of_one_le hsRatio hExpE
  have hprod := product_threshold_le hn hkm hd hk hβ hμ
  have hnum : 1+productThreshold (4*k) (d/2) (scale n k β μ)
      (sqrt k*scale n k β μ) (candidateBudget n k β) ≤
      (1+50*sqrt GaussianAppend.appendConstant)*(sqrt k/μ)*
        exp ((2*β+6)*loss n k d) := by
    nlinarith only [hunit,hprod]
  have hci := compression_inverse_le hn hkm hd hk β
  have hcp := compression_pos (show 0< k by omega) (show 2≤ d by omega) (theta_pos n k d β)
  have hnum0 : 0≤1+productThreshold (4*k) (d/2) (scale n k β μ)
      (sqrt k*scale n k β μ) (candidateBudget n k β) := by
    have hscale := (scale_pos (n:=n) (k:=k) β hμ).le
    have hx := (budgets_pos (k:=k) (show 1< n by omega) hβ).2.le
    unfold productThreshold
    positivity
  have hfrac : (1+productThreshold (4*k) (d/2) (scale n k β μ)
      (sqrt k*scale n k β μ) (candidateBudget n k β))/
        compressionThreshold (4*k) (d/2) (theta n k d β) ≤
      24*exp 1*(1+50*sqrt GaussianAppend.appendConstant)*((k:ℝ)/(μ*d))*
        exp ((thetaCoefficient β+2*β+6)*(1+loss n k d)) := by
    calc
      _ ≤ ((1+50*sqrt GaussianAppend.appendConstant)*(sqrt k/μ)*
          exp ((2*β+6)*loss n k d))*
          (24*exp 1*sqrt k/(d:ℝ)*exp (thetaCoefficient β*(1+loss n k d))) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul hnum hci (inv_nonneg.mpr hcp.le) (by positivity)
      _ = 24*exp 1*(1+50*sqrt GaussianAppend.appendConstant)*((k:ℝ)/(μ*d))*
          exp ((2*β+6)*loss n k d+thetaCoefficient β*(1+loss n k d)) := by
        rw [exp_add]
        have hs := sq_sqrt hkR.le
        field_simp
        nlinarith only [hs]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by positivity)
        nlinarith only [hE]
  have haExp : firstBudget n β/(k:ℝ)≤
      (thetaCoefficient β+2*β+6)*(1+loss n k d) := by
    have h1 := mul_le_mul_of_nonneg_left hcomp.1 (by linarith : 0≤β+1)
    have h2 := mul_nonneg (by linarith : 0≤ thetaCoefficient β+β+5) hz
    unfold firstBudget
    rw [mul_div_assoc]
    nlinarith only [h1,h2,hD,hE]
  have ha : scale n k β μ ≤ sqrt GaussianAppend.appendConstant*((k:ℝ)/(μ*d))*
      exp ((thetaCoefficient β+2*β+6)*(1+loss n k d)) := by
    have hc : μ⁻¹≤(k:ℝ)/(μ*d) := by
      apply (le_div_iff₀ (mul_pos hμ hdR)).mpr
      simpa [hμ.ne',mul_assoc] using hdk
    unfold scale
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hc (sqrt_nonneg _)) (exp_le_exp.mpr haExp)
      (exp_nonneg _) (by positivity)
  unfold denominatorConstant
  have hrem : 0≤((k:ℝ)/(μ*d))*exp ((thetaCoefficient β+2*β+6)*(1+loss n k d)) := by positivity
  nlinarith only [ha,hfrac,hrem]


theorem exponential_absorption {H B z : ℝ} (hH : 1≤ H) (hz : 0≤ z) :
    exp (-(B+log (2*H)+1)*(1+z))≤(2*H)⁻¹*exp (-B*(1+z)) := by
  have hHpos : 0<2*H := by linarith
  have hlog : 0≤ log (2*H) := log_nonneg (by linarith)
  rw [← exp_log hHpos,← exp_neg,← exp_add]
  apply exp_le_exp.mpr
  simp only [log_exp]
  have hh := mul_nonneg (by linarith : 0≤ log (2*H)+1) hz
  nlinarith only [hh]

theorem source_threshold_le {n m k d : ℕ} (hn : m+4*k≤ n) (hkm : k < m)
    (hd : 16≤ d) (hk : 100*d≤ k) {β μ : ℝ} (hβ : 1≤β) (hμ : 0<μ)
    (hμk : μ≤ sqrt k) :
    (μ*d/k)*exp (-extensionConstant β*(1+loss n k d)) ≤
      stackingThreshold (4*k) (d/2) (scale n k β μ) (sqrt k*scale n k β μ)
        (candidateBudget n k β) (theta n k d β) := by
  have hk0 : 0< k := by omega
  have hd0 : 0< d := by omega
  have hn0 : 1≤ n := by omega
  have hkR : (0:ℝ)< k := by exact_mod_cast hk0
  have hdR : (0:ℝ)< d := by exact_mod_cast hd0
  have hden := stacking_denominator_le hn hkm hd hk hβ hμ hμk
  have hscale := scale_pos (n:=n) (k:=k) β hμ
  have hcp := compression_pos hk0 (show 2≤ d by omega) (theta_pos n k d β)
  have hx := (budgets_pos (k:=k) (show 1< n by omega) hβ).2
  have hu : 0≤ productThreshold (4*k) (d/2) (scale n k β μ)
      (sqrt k*scale n k β μ) (candidateBudget n k β) := by
    unfold productThreshold
    positivity
  have hp : 0< scale n k β μ+
      (1+productThreshold (4*k) (d/2) (scale n k β μ) (sqrt k*scale n k β μ)
        (candidateBudget n k β))/compressionThreshold (4*k) (d/2) (theta n k d β) := by
    positivity
  have hH := denominatorConstant_ge_one
  have habs := exponential_absorption (B:=thetaCoefficient β+2*β+6)
    hH (loss_nonneg (k:=k) (d:=d) hn0)
  have hscalar : (μ*d/k)*exp (-extensionConstant β*(1+loss n k d)) ≤
      (denominatorConstant*((k:ℝ)/(μ*d))*
        exp ((thetaCoefficient β+2*β+6)*(1+loss n k d)))⁻¹/2 := by
    calc
      _ ≤ (μ*d/k)*((2*denominatorConstant)⁻¹*
          exp (-(thetaCoefficient β+2*β+6)*(1+loss n k d))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact habs
      _ = _ := by
        rw [show -(thetaCoefficient β+2*β+6)*(1+loss n k d)=
          -((thetaCoefficient β+2*β+6)*(1+loss n k d)) by ring,exp_neg]
        simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
        ring
  exact hscalar.trans (div_le_div_of_nonneg_right (inv_anti₀ hp hden) (by norm_num))

#assert_trust kernel loss
#print axioms loss
#assert_trust kernel thetaCoefficient
#print axioms thetaCoefficient
#assert_trust kernel theta
#print axioms theta
#assert_trust kernel firstBudget
#print axioms firstBudget
#assert_trust kernel candidateBudget
#print axioms candidateBudget
#assert_trust kernel scale
#print axioms scale
#assert_trust kernel denominatorConstant
#print axioms denominatorConstant
#assert_trust kernel extensionConstant
#print axioms extensionConstant
#assert_trust kernel dimensions
#print axioms dimensions
#assert_trust kernel loss_nonneg
#print axioms loss_nonneg
#assert_trust kernel theta_pos
#print axioms theta_pos
#assert_trust kernel theta_le_one
#print axioms theta_le_one
#assert_trust kernel budgets_pos
#print axioms budgets_pos
#assert_trust kernel scale_pos
#print axioms scale_pos
#assert_trust kernel denominatorConstant_ge_one
#print axioms denominatorConstant_ge_one
#assert_trust kernel extensionConstant_pos
#print axioms extensionConstant_pos
#assert_trust kernel candidate_exponent_bound
#print axioms candidate_exponent_bound
#assert_trust kernel overcrowding_term_le
#print axioms overcrowding_term_le
#assert_trust kernel probability_accounting
#print axioms probability_accounting
#assert_trust kernel loss_comparisons
#print axioms loss_comparisons
#assert_trust kernel candidate_root_le
#print axioms candidate_root_le
#assert_trust kernel two_sqrt_le_exp
#print axioms two_sqrt_le_exp
#assert_trust kernel product_threshold_le
#print axioms product_threshold_le
#assert_trust kernel compression_pos
#print axioms compression_pos
#assert_trust kernel compression_inverse_le
#print axioms compression_inverse_le
#assert_trust kernel stacking_denominator_le
#print axioms stacking_denominator_le
#assert_trust kernel exponential_absorption
#print axioms exponential_absorption
#assert_trust kernel source_threshold_le
#print axioms source_threshold_le
end NLA.IE06.SelectedBlockExtensionScalars
