import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic

/-!
# The actual scalar Bessel kernel series

The factorial series converges absolutely at every real argument, uniformly
on every bounded interval. Its definition is independent of later Laplace
integration and asymptotic estimates.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace ProofProject

def besselTerm (n : ℕ) (u : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * u ^ n / ((n.factorial : ℝ) * ((n + 1).factorial : ℝ))

def besselKernel (u : ℝ) : ℝ := ∑' n : ℕ, besselTerm n u

theorem norm_besselTerm (n : ℕ) (u : ℝ) :
    ‖besselTerm n u‖ = ‖u‖ ^ n / ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)) := by
  simp only [besselTerm, norm_div, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, Real.norm_of_nonneg (Nat.cast_nonneg _)]

theorem norm_besselTerm_le (n : ℕ) (u : ℝ) :
    ‖besselTerm n u‖ ≤ ‖u‖ ^ n / (n.factorial : ℝ) := by
  rw [norm_besselTerm]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have h : (1 : ℝ) ≤ ((n + 1).factorial : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos (n + 1)))
  nlinarith [show (0 : ℝ) ≤ n.factorial by positivity]

theorem norm_besselTerm_le_of_norm_le (n : ℕ) {u R : ℝ} (hu : ‖u‖ ≤ R) :
    ‖besselTerm n u‖ ≤ R ^ n / (n.factorial : ℝ) :=
  (norm_besselTerm_le n u).trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hu n) (by positivity))

theorem besselTerm_summable (u : ℝ) : Summable (fun n : ℕ => besselTerm n u) :=
  (Real.summable_pow_div_factorial ‖u‖).of_norm_bounded (fun n => norm_besselTerm_le n u)

theorem besselTerm_norm_summable (u : ℝ) : Summable (fun n : ℕ => ‖besselTerm n u‖) :=
  (Real.summable_pow_div_factorial ‖u‖).of_nonneg_of_le
    (fun n => norm_nonneg _) (fun n => norm_besselTerm_le n u)

theorem besselTerm_hasSum (u : ℝ) : HasSum (fun n : ℕ => besselTerm n u) (besselKernel u) :=
  (besselTerm_summable u).hasSum

theorem besselTerm_continuous (n : ℕ) : Continuous (besselTerm n) := by
  unfold besselTerm
  fun_prop

theorem besselKernel_uniformOn (R : ℝ) :
    TendstoUniformlyOn (fun N : ℕ => fun u : ℝ =>
      ∑ n ∈ Finset.range N, besselTerm n u) besselKernel atTop (Icc (-R) R) := by
  apply tendstoUniformlyOn_tsum_nat (Real.summable_pow_div_factorial R)
  intro n u hu
  exact norm_besselTerm_le_of_norm_le n
    (by simpa only [Real.norm_eq_abs, abs_le, mem_Icc] using hu)

theorem besselKernel_continuousOn (R : ℝ) : ContinuousOn besselKernel (Icc (-R) R) := by
  apply (besselKernel_uniformOn R).continuousOn
  exact Filter.Frequently.of_forall fun N =>
    (continuous_finsetSum _ (fun n _ => besselTerm_continuous n)).continuousOn

theorem besselKernel_continuous : Continuous besselKernel := by
  rw [continuous_iff_continuousAt]
  intro u
  apply (besselKernel_continuousOn (‖u‖ + 1)).continuousAt
  apply Icc_mem_nhds
  · have h : -‖u‖ ≤ u := by simpa only [Real.norm_eq_abs] using neg_abs_le u
    linarith
  · have h : u ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using le_abs_self u
    linarith

@[simp] theorem besselKernel_zero : besselKernel 0 = 1 := by
  rw [besselKernel, tsum_eq_single 0]
  · norm_num [besselTerm]
  · intro n hn
    simp [besselTerm, zero_pow hn]

end ProofProject
