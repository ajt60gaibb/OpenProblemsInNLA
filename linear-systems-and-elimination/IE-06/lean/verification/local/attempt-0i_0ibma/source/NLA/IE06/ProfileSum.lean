/- Exact finite profile bound for the retained inverse sum. Approved contract:
reviews/profile-sum-preimplementation-review.md. -/
import NLA.IE06.TruncatedInverse
import NLA.IE06.ScalarRecurrence

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.IE06.ProfileSum
open Spectral TruncatedInverse

theorem inv_sq_le_telescoping {d : ℕ} (hd : 0 < d) :
    (d : ℝ)⁻¹^2 ≤ 2 * ((d : ℝ)⁻¹ - ((d+1 : ℕ) : ℝ)⁻¹) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : (0 : ℝ) < (d : ℝ)+1 := by positivity
  rw [Nat.cast_add,Nat.cast_one]
  field_simp
  nlinarith

theorem sum_inv_sq_le_telescoping {r t : ℕ} (hr : 0 < r) (hrt : r ≤ t) :
    (∑ d ∈ Finset.Ico r t, (d : ℝ)⁻¹^2) ≤
      2 * ((r : ℝ)⁻¹ - (t : ℝ)⁻¹) := by
  induction t, hrt using Nat.le_induction with
  | base => simp
  | succ t hrt ih =>
    rw [Finset.sum_Ico_succ_top hrt]
    have ht := inv_sq_le_telescoping (hr.trans_le hrt)
    linarith

theorem sum_inv_sq_le {r t : ℕ} (hr : 0 < r) :
    (∑ d ∈ Finset.Ico r t, (d : ℝ)⁻¹^2) ≤ 2 / (r : ℝ) := by
  by_cases hrt : r ≤ t
  · have h := sum_inv_sq_le_telescoping hr hrt
    have hn : (0 : ℝ) ≤ (t : ℝ)⁻¹ := by positivity
    simpa only [div_eq_mul_inv] using (by linarith :
      (∑ d ∈ Finset.Ico r t, (d : ℝ)⁻¹^2) ≤ 2 * (r : ℝ)⁻¹)
  · simp only [Finset.Ico_eq_empty_of_le (by omega : t ≤ r),Finset.sum_empty]
    positivity

theorem sigmaInvSum_eq_sum_Ico {t r : ℕ} (T : Matrix (Fin t) (Fin t) ℝ)
    (hrt : r ≤ t) :
    sigmaInvSum T r = ∑ d ∈ Finset.Ico r t, (singularValue T (t-d-1))⁻¹^2 := by
  unfold sigmaInvSum
  refine Finset.sum_bij (fun i _ => t-i.val-1) ?_ ?_ ?_ ?_
  · intro i _
    exact Finset.mem_Ico.mpr (by have := i.isLt; omega)
  · intro i _ j _ he
    apply Fin.ext
    have := i.isLt
    have := j.isLt
    omega
  · intro d hd
    obtain ⟨hdr,hdt⟩ := Finset.mem_Ico.mp hd
    refine ⟨⟨t-d-1,by omega⟩,Finset.mem_univ _,?_⟩
    dsimp
    omega
  · intro i _
    have he : t-(t-i.val-1)-1=i.val := by have := i.isLt; omega
    rw [he]

/-- A positive linear-in-index profile bounds each actual retained reciprocal. -/
theorem inv_singularValue_le_profile {t r d : ℕ} (T : Matrix (Fin t) (Fin t) ℝ)
    (g : ℕ → ℝ) (hr : 0 < r) (hdr : r ≤ d) (hg : 0 < g r)
    (hratio : g r / r ≤ g d / d) (hs : g d ≤ singularValue T (t-d-1)) :
    (singularValue T (t-d-1))⁻¹ ≤ (r / g r) * (d : ℝ)⁻¹ := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hdR : (0 : ℝ) < d := by exact_mod_cast hr.trans_le hdr
  have hp : 0 < (g r / r) * d := mul_pos (div_pos hg hrR) hdR
  have hl : (g r / r) * d ≤ singularValue T (t-d-1) :=
    ((le_div_iff₀ hdR).mp hratio).trans hs
  calc
    _ ≤ ((g r / r) * d)⁻¹ := inv_anti₀ hp hl
    _ = _ := by simp only [mul_inv_rev,inv_div]; ring

/-- The exact source bound, with an empty retained range included. -/
theorem sigmaInvSum_le_profile {t r : ℕ} (T : Matrix (Fin t) (Fin t) ℝ)
    (g : ℕ → ℝ) (hr : 0 < r) (hg : 0 < g r)
    (hratio : ∀ d, r ≤ d → d < t → g r / r ≤ g d / d)
    (hs : ∀ d, r ≤ d → d < t → g d ≤ singularValue T (t-d-1)) :
    sigmaInvSum T r ≤ 2 * r / (g r)^2 := by
  by_cases htr : t ≤ r
  · rw [sigmaInvSum_eq_zero_of_le T htr]
    positivity
  have hrt : r ≤ t := by omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  rw [sigmaInvSum_eq_sum_Ico T hrt]
  calc
    _ ≤ ∑ d ∈ Finset.Ico r t, (r / g r)^2 * (d : ℝ)⁻¹^2 := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hdr,hdt⟩ := Finset.mem_Ico.mp hd
      have hi := inv_singularValue_le_profile T g hr hdr hg (hratio d hdr hdt) (hs d hdr hdt)
      simpa only [mul_pow] using pow_le_pow_left₀
        (inv_nonneg.mpr (singularValue_nonneg T _)) hi 2
    _ = (r / g r)^2 * ∑ d ∈ Finset.Ico r t, (d : ℝ)⁻¹^2 := by rw [Finset.mul_sum]
    _ ≤ (r / g r)^2 * (2 / r) :=
      mul_le_mul_of_nonneg_left (sum_inv_sq_le hr) (sq_nonneg _)
    _ = 2 * r / (g r)^2 := by field_simp

/-- Specialization to the genuinely proved finite-recursion threshold profile. -/
theorem sigmaInvSum_le_scalarProfile {n t r : ℕ} (T : Matrix (Fin t) (Fin t) ℝ)
    {ℓ D : ℝ} (hn : 0 < n) (hr : 0 < r) (hℓ : 0 < ℓ) (hD : 0 ≤ D)
    (hs : ∀ d, r ≤ d → d < t →
      ScalarRecurrence.profile n ℓ D d ≤ singularValue T (t-d-1)) :
    sigmaInvSum T r ≤ 2 * r / (ScalarRecurrence.profile n ℓ D r)^2 := by
  apply sigmaInvSum_le_profile T (ScalarRecurrence.profile n ℓ D) hr
    (ScalarRecurrence.profile_pos hn hr ℓ D) _ hs
  exact fun _ hdr _ => ScalarRecurrence.profile_ratio_monotone hℓ hD hr hdr

#assert_trust kernel inv_sq_le_telescoping
#print axioms inv_sq_le_telescoping
#assert_trust kernel sum_inv_sq_le_telescoping
#print axioms sum_inv_sq_le_telescoping
#assert_trust kernel sum_inv_sq_le
#print axioms sum_inv_sq_le
#assert_trust kernel sigmaInvSum_eq_sum_Ico
#print axioms sigmaInvSum_eq_sum_Ico
#assert_trust kernel inv_singularValue_le_profile
#print axioms inv_singularValue_le_profile
#assert_trust kernel sigmaInvSum_le_profile
#print axioms sigmaInvSum_le_profile
#assert_trust kernel sigmaInvSum_le_scalarProfile
#print axioms sigmaInvSum_le_scalarProfile

end NLA.IE06.ProfileSum
