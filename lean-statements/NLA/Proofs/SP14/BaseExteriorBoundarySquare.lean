import NLA.Proofs.SP14.BaseExteriorSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
The normalized exterior boundary series satisfies its square equation at
every circle point, including its two zeros. The proof uses an absolutely
convergent Cauchy product at the boundary.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- Boundary square identity for the already normalized exterior branch. -/
theorem baseExteriorSymbol_sq (z : Circle) :
    baseExteriorSymbol z ^ 2 = (z : ℂ) ^ 2 + 1 := by
  let f : ℕ → ℂ := fun n => baseCoeff n * (z : ℂ) ^ (1 - 2 * (n : ℤ))
  have hz : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
  have hf : Summable (fun n : ℕ => ‖f n‖) := by
    simpa [f, norm_mul, norm_zpow, Circle.norm_coe] using summable_norm_baseCoeff
  have hconv (n : ℕ) :
      (∑ kl ∈ Finset.antidiagonal n, f kl.1 * f kl.2) =
        ((if n = 0 then 1 else 0) + (if n = 1 then 1 else 0)) *
          (z : ℂ) ^ (2 - 2 * (n : ℤ)) := by
    calc
      (∑ kl ∈ Finset.antidiagonal n, f kl.1 * f kl.2) =
          ∑ kl ∈ Finset.antidiagonal n,
            (baseCoeff kl.1 * baseCoeff kl.2) *
              (z : ℂ) ^ (2 - 2 * (n : ℤ)) := by
        apply Finset.sum_congr rfl
        intro kl hkl
        have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
        have hsumz : (kl.1 : ℤ) + (kl.2 : ℤ) = (n : ℤ) := by exact_mod_cast hsum
        have hexp : (1 - 2 * (kl.1 : ℤ)) + (1 - 2 * (kl.2 : ℤ)) =
            2 - 2 * (n : ℤ) := by omega
        dsimp [f]
        rw [mul_mul_mul_comm, ← zpow_add₀ hz]
        rw [hexp]
      _ = (∑ kl ∈ Finset.antidiagonal n,
            baseCoeff kl.1 * baseCoeff kl.2) *
              (z : ℂ) ^ (2 - 2 * (n : ℤ)) := by rw [Finset.sum_mul]
      _ = _ := by rw [baseCoeff_convolution]
  calc
    baseExteriorSymbol z ^ 2 = (∑' n : ℕ, f n) * (∑' n : ℕ, f n) := by
      simp [baseExteriorSymbol, f, pow_two]
    _ = ∑' n : ℕ, ∑ kl ∈ Finset.antidiagonal n, f kl.1 * f kl.2 :=
      tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hf
    _ = ∑' n : ℕ,
          ((if n = 0 then 1 else 0) + (if n = 1 then 1 else 0)) *
            (z : ℂ) ^ (2 - 2 * (n : ℤ)) := by
      apply tsum_congr
      exact hconv
    _ = (z : ℂ) ^ 2 + 1 := by
      rw [tsum_eq_sum (s := {0, 1})]
      · simp
      · intro n hn
        have hh : n ≠ 0 ∧ n ≠ 1 := by simpa using hn
        rcases hh with ⟨h0, h1⟩
        simp [h0, h1]

/-- The normalized exterior boundary series vanishes at both circle points
where `z² = -1`. -/
theorem baseExteriorSymbol_zero_of_sq_eq_neg_one (z : Circle)
    (hz : (z : ℂ) ^ 2 = -1) : baseExteriorSymbol z = 0 := by
  have hsq : baseExteriorSymbol z ^ 2 = 0 := by
    rw [baseExteriorSymbol_sq, hz]
    ring
  exact eq_zero_of_pow_eq_zero hsq

#assert_trust kernel baseExteriorSymbol_sq
#assert_trust kernel baseExteriorSymbol_zero_of_sq_eq_neg_one
#print axioms baseExteriorSymbol_zero_of_sq_eq_neg_one

end NLA.Proofs.SP14
