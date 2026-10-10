import NLA.Proofs.SP14.BaseCoefficient
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
Absolute summability of the normalized half-binomial coefficients via an
exact telescoping recurrence, including the `n=0` endpoint.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

private theorem baseCoeff_succ_mul (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) * baseCoeff (n + 1) =
      ((1 / 2 : ℂ) - n) * baseCoeff n := by
  unfold baseCoeff
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul]
  simp only [smul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  rw [descPochhammer_succ_right, Polynomial.smeval_mul,
    Polynomial.smeval_sub]
  simp only [Polynomial.smeval_X, Polynomial.smeval_natCast, pow_zero, mul_one,
    nsmul_eq_mul]
  have hf : ((n.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp [hf, hn]

private theorem baseCoeff_norm_succ (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) + 1) * ‖baseCoeff (n + 1)‖ =
      ((n : ℝ) - 1 / 2) * ‖baseCoeff n‖ := by
  have hnonpos : (1 / 2 : ℝ) - n ≤ 0 := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hfactor : ‖(1 / 2 : ℂ) - (n : ℂ)‖ = (n : ℝ) - 1 / 2 := by
    have hcast : (1 / 2 : ℂ) - (n : ℂ) = (((1 / 2 : ℝ) - n : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hnonpos]
    ring
  have h := congrArg norm (baseCoeff_succ_mul n)
  have hnat : ‖((n + 1 : ℕ) : ℂ)‖ = (n : ℝ) + 1 := by
    rw [Complex.norm_natCast]
    push_cast
    ring
  rw [norm_mul, norm_mul, hnat, hfactor] at h
  exact h

theorem summable_norm_baseCoeff : Summable (fun n : ℕ => ‖baseCoeff n‖) := by
  let a : ℕ → ℝ := fun n => ‖baseCoeff n‖
  have hzero : a 0 = 1 := by simp [a, baseCoeff]
  have hone : a 1 = 1 / 2 := by norm_num [a, baseCoeff, Ring.choose_one_right]
  have htel (N : ℕ) :
      (∑ n ∈ Finset.range N, a (n + 1)) =
        1 - 2 * ((N : ℝ) + 1) * a (N + 1) := by
    induction N with
    | zero => simp [hone]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hr := baseCoeff_norm_succ (N + 1) (by omega : 1 ≤ N + 1)
      dsimp [a] at hr ⊢
      push_cast at hr ⊢
      nlinarith
  have hbound (N : ℕ) : (∑ n ∈ Finset.range N, a n) ≤ 2 := by
    cases N with
    | zero => simp
    | succ N =>
      rw [Finset.sum_range_succ', htel, hzero]
      have hnonneg : 0 ≤ a (N + 1) := norm_nonneg _
      nlinarith
  exact summable_of_sum_range_le (fun n => norm_nonneg _) hbound

#assert_trust kernel summable_norm_baseCoeff
#print axioms summable_norm_baseCoeff

end NLA.Proofs.SP14
