import ProofProject.BesselKernelSeries
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Differentiation and the scalar Bessel equation

A shifted-factorial family makes all derivatives explicit. The derivative
series converge uniformly on bounded intervals, so termwise differentiation
is justified before the coefficient recurrence is summed.
-/

noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace ProofProject

def besselOrderTerm (k n : ℕ) (u : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * u ^ n / ((n.factorial : ℝ) * ((n + k).factorial : ℝ))

def besselOrderKernel (k : ℕ) (u : ℝ) : ℝ := ∑' n : ℕ, besselOrderTerm k n u

theorem besselOrderKernel_one : besselOrderKernel 1 = besselKernel := rfl

theorem norm_besselOrderTerm_le (k n : ℕ) {u R : ℝ} (hu : ‖u‖ ≤ R) :
    ‖besselOrderTerm k n u‖ ≤ R ^ n / (n.factorial : ℝ) := by
  simp only [besselOrderTerm, norm_div, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ ‖u‖ ^ n / (n.factorial : ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have h : (1 : ℝ) ≤ ((n + k).factorial : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos (n + k)))
      nlinarith [show (0 : ℝ) ≤ n.factorial by positivity]
    _ ≤ _ := div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hu n) (by positivity)

theorem besselOrderTerm_summable (k : ℕ) (u : ℝ) :
    Summable (fun n : ℕ => besselOrderTerm k n u) :=
  (Real.summable_pow_div_factorial ‖u‖).of_norm_bounded
    (fun n => norm_besselOrderTerm_le k n le_rfl)

theorem besselOrderTerm_tail_summable (k : ℕ) (u : ℝ) :
    Summable (fun n : ℕ => besselOrderTerm k (n + 1) u) :=
  (summable_nat_add_iff 1).mpr (besselOrderTerm_summable k u)

@[simp] theorem besselOrderTerm_zero (k : ℕ) (u : ℝ) :
    besselOrderTerm k 0 u = 1 / (k.factorial : ℝ) := by
  simp [besselOrderTerm]

theorem besselOrderKernel_split (k : ℕ) (u : ℝ) :
    besselOrderKernel k u = 1 / (k.factorial : ℝ) +
      ∑' n : ℕ, besselOrderTerm k (n + 1) u := by
  simpa only [besselOrderKernel, besselOrderTerm_zero] using
    (besselOrderTerm_summable k u).tsum_eq_zero_add

theorem besselOrderTerm_succ_hasDerivAt (k n : ℕ) (u : ℝ) :
    HasDerivAt (besselOrderTerm k (n + 1)) (-besselOrderTerm (k + 1) n u) u := by
  have h := ((hasDerivAt_pow (n + 1) u).const_mul ((-1 : ℝ) ^ (n + 1))).div_const
    (((n + 1).factorial : ℝ) * ((n + 1 + k).factorial : ℝ))
  have hc : (-1 : ℝ) ^ (n + 1) * (((n + 1 : ℕ) : ℝ) * u ^ n) /
      (((n + 1).factorial : ℝ) * ((n + 1 + k).factorial : ℝ)) =
      -besselOrderTerm (k + 1) n u := by
    simp only [besselOrderTerm, pow_succ,
      show n + 1 + k = n + (k + 1) by omega, Nat.factorial_succ n,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    have hnk : ((n + (k + 1)).factorial : ℝ) ≠ 0 := by positivity
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  simp only [Nat.add_sub_cancel] at h
  rw [hc] at h
  simpa only [besselOrderTerm] using! h

/-- Every member has derivative minus the next member; differentiation is
justified on a bounded open interval about the evaluation point. -/
theorem besselOrderKernel_hasDerivAt (k : ℕ) (u : ℝ) :
    HasDerivAt (besselOrderKernel k) (-besselOrderKernel (k + 1) u) u := by
  let R : ℝ := ‖u‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hu : u ∈ Ioo (-R) R := by
    have hl : -‖u‖ ≤ u := by simpa only [Real.norm_eq_abs] using neg_abs_le u
    have hr : u ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using le_abs_self u
    simp only [Real.norm_eq_abs] at hl hr
    constructor <;> dsimp [R] <;> linarith
  have htail := hasDerivAt_tsum_of_isPreconnected
    (Real.summable_pow_div_factorial R) isOpen_Ioo (convex_Ioo (-R) R).isPreconnected
    (fun n v (_ : v ∈ Ioo (-R) R) => besselOrderTerm_succ_hasDerivAt k n v)
    (fun n v hv => show ‖-besselOrderTerm (k + 1) n v‖ ≤ R ^ n / (n.factorial : ℝ) from by
      rw [norm_neg]
      apply norm_besselOrderTerm_le
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨hv.1.le, hv.2.le⟩)
    (show (0 : ℝ) ∈ Ioo (-R) R from ⟨by linarith, hR⟩)
    (besselOrderTerm_tail_summable k 0) hu
  have htail' : HasDerivAt (fun v => ∑' n : ℕ, besselOrderTerm k (n + 1) v)
      (-besselOrderKernel (k + 1) u) u := by
    simpa only [tsum_neg, besselOrderKernel] using htail
  have heq : besselOrderKernel k = fun v => 1 / (k.factorial : ℝ) +
      ∑' n : ℕ, besselOrderTerm k (n + 1) v := by
    funext v
    exact besselOrderKernel_split k v
  rw [heq]
  exact htail'.const_add _

theorem deriv_besselOrderKernel (k : ℕ) :
    deriv (besselOrderKernel k) = fun u => -besselOrderKernel (k + 1) u := by
  funext u
  exact (besselOrderKernel_hasDerivAt k u).deriv

theorem besselOrderKernel_differentiable (k : ℕ) : Differentiable ℝ (besselOrderKernel k) :=
  fun u => (besselOrderKernel_hasDerivAt k u).differentiableAt

theorem besselOrderKernel_contDiff_nat (m : ℕ) (k : ℕ) :
    ContDiff ℝ m (besselOrderKernel k) := by
  induction m generalizing k with
  | zero => exact contDiff_zero.mpr (besselOrderKernel_differentiable k).continuous
  | succ m ih =>
      rw [Nat.cast_add_one, contDiff_succ_iff_deriv, deriv_besselOrderKernel]
      exact ⟨besselOrderKernel_differentiable k, by simp, (ih (k + 1)).neg⟩

theorem besselOrderKernel_contDiff (k : ℕ) : ContDiff ℝ ∞ (besselOrderKernel k) :=
  contDiff_infty.mpr (fun m => besselOrderKernel_contDiff_nat m k)

theorem besselKernel_contDiff : ContDiff ℝ ∞ besselKernel :=
  besselOrderKernel_contDiff 1

theorem besselKernel_hasDerivAt (u : ℝ) :
    HasDerivAt besselKernel (-besselOrderKernel 2 u) u :=
  besselOrderKernel_hasDerivAt 1 u

theorem deriv_besselKernel (u : ℝ) : deriv besselKernel u = -besselOrderKernel 2 u :=
  (besselKernel_hasDerivAt u).deriv

theorem besselKernel_deriv_hasDerivAt (u : ℝ) :
    HasDerivAt (deriv besselKernel) (besselOrderKernel 3 u) u := by
  have heq : deriv besselKernel = fun v => -besselOrderKernel 2 v := funext deriv_besselKernel
  rw [heq]
  simpa only [neg_neg] using! (besselOrderKernel_hasDerivAt 2 u).neg

theorem deriv_deriv_besselKernel (u : ℝ) :
    deriv (deriv besselKernel) u = besselOrderKernel 3 u :=
  (besselKernel_deriv_hasDerivAt u).deriv

private theorem besselOrderTerm_recurrence (n : ℕ) (u : ℝ) :
    besselOrderTerm 1 (n + 1) u =
      2 * besselOrderTerm 2 (n + 1) u - u * besselOrderTerm 3 n u := by
  simp only [besselOrderTerm, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat, pow_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
  field_simp
  ring

theorem besselOrderKernel_recurrence (u : ℝ) :
    besselOrderKernel 1 u = 2 * besselOrderKernel 2 u - u * besselOrderKernel 3 u := by
  have hsum : (∑' n : ℕ, besselOrderTerm 1 (n + 1) u) =
      2 * (∑' n : ℕ, besselOrderTerm 2 (n + 1) u) - u * besselOrderKernel 3 u := by
    simp_rw [besselOrderTerm_recurrence]
    rw [Summable.tsum_sub ((besselOrderTerm_tail_summable 2 u).mul_left 2)
      ((besselOrderTerm_summable 3 u).mul_left u), tsum_mul_left, tsum_mul_left]
    rfl
  have h1 := besselOrderKernel_split 1 u
  have h2 := besselOrderKernel_split 2 u
  norm_num at h1 h2
  linarith

/-- The actual factorial series satisfies its differential equation at every
real argument, including the regular endpoint zero. -/
theorem besselKernel_ode (u : ℝ) :
    u * deriv (deriv besselKernel) u + 2 * deriv besselKernel u + besselKernel u = 0 := by
  rw [deriv_besselKernel, deriv_deriv_besselKernel, ← besselOrderKernel_one,
    besselOrderKernel_recurrence]
  ring

end ProofProject
