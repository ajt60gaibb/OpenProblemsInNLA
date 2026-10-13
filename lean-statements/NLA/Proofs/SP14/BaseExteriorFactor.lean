import NLA.Proofs.SP14.BaseExteriorBoundarySquare
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
The normalized exterior square-root factor on the circle. Its coefficient
series selects the branch, including at the boundary zeros. Holomorphy on
the exterior domain and perturbed-background bounds are separate obligations.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- Boundary trace of the normalized exterior series `sqrt(1+s⁻¹)`. -/
noncomputable def baseExteriorFactor (s : Circle) : ℂ :=
  ∑' n : ℕ, baseCoeff n * (s : ℂ) ^ (-(n : ℤ))

private theorem baseExteriorFactor_term_norm (n : ℕ) (s : Circle) :
    ‖baseCoeff n * (s : ℂ) ^ (-(n : ℤ))‖ = ‖baseCoeff n‖ := by
  rw [norm_mul, norm_zpow, Circle.norm_coe, one_zpow, mul_one]

theorem summable_baseExteriorFactor_terms (s : Circle) :
    Summable (fun n : ℕ => baseCoeff n * (s : ℂ) ^ (-(n : ℤ))) := by
  apply Summable.of_norm_bounded summable_norm_baseCoeff
  intro n
  rw [baseExteriorFactor_term_norm]

theorem continuous_baseExteriorFactor : Continuous baseExteriorFactor := by
  unfold baseExteriorFactor
  apply continuous_tsum
  · intro n
    have hp : Continuous (fun s : Circle => (s : Circle) ^ (-(n : ℤ))) :=
      continuous_zpow _
    have hcoe : Continuous (fun s : Circle => (s : ℂ) ^ (-(n : ℤ))) := by
      apply (continuous_subtype_val.comp hp).congr
      intro s
      exact Circle.coe_zpow s _
    exact continuous_const.mul hcoe
  · exact summable_norm_baseCoeff
  · intro n s
    rw [baseExteriorFactor_term_norm]

theorem baseExteriorFactor_sq (s : Circle) :
    baseExteriorFactor s ^ 2 = 1 + (s : ℂ)⁻¹ := by
  let f : ℕ → ℂ := fun n => baseCoeff n * (s : ℂ) ^ (-(n : ℤ))
  have hs : (s : ℂ) ≠ 0 := Circle.coe_ne_zero s
  have hf : Summable (fun n : ℕ => ‖f n‖) := by
    simpa [f, norm_mul, norm_zpow, Circle.norm_coe] using summable_norm_baseCoeff
  have hconv (n : ℕ) :
      (∑ kl ∈ Finset.antidiagonal n, f kl.1 * f kl.2) =
        ((if n = 0 then 1 else 0) + (if n = 1 then 1 else 0)) *
          (s : ℂ) ^ (-(n : ℤ)) := by
    calc
      (∑ kl ∈ Finset.antidiagonal n, f kl.1 * f kl.2) =
          ∑ kl ∈ Finset.antidiagonal n,
            (baseCoeff kl.1 * baseCoeff kl.2) *
              (s : ℂ) ^ (-(n : ℤ)) := by
        apply Finset.sum_congr rfl
        intro kl hkl
        have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
        have hsumz : (kl.1 : ℤ) + (kl.2 : ℤ) = (n : ℤ) := by exact_mod_cast hsum
        have hexp : -(kl.1 : ℤ) + -(kl.2 : ℤ) = -(n : ℤ) := by omega
        dsimp [f]
        rw [mul_mul_mul_comm, ← zpow_add₀ hs]
        rw [hexp]
      _ = (∑ kl ∈ Finset.antidiagonal n,
            baseCoeff kl.1 * baseCoeff kl.2) *
              (s : ℂ) ^ (-(n : ℤ)) := by rw [Finset.sum_mul]
      _ = _ := by rw [baseCoeff_convolution]
  calc
    baseExteriorFactor s ^ 2 = (∑' n : ℕ, f n) * (∑' n : ℕ, f n) := by
      simp [baseExteriorFactor, f, pow_two]
    _ = ∑' n : ℕ, ∑ kl ∈ Finset.antidiagonal n, f kl.1 * f kl.2 :=
      tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hf
    _ = ∑' n : ℕ,
          ((if n = 0 then 1 else 0) + (if n = 1 then 1 else 0)) *
            (s : ℂ) ^ (-(n : ℤ)) := by
      apply tsum_congr
      exact hconv
    _ = 1 + (s : ℂ)⁻¹ := by
      rw [tsum_eq_sum (s := {0, 1})]
      · simp
      · intro n hn
        have hh : n ≠ 0 ∧ n ≠ 1 := by simpa using hn
        rcases hh with ⟨h0, h1⟩
        simp [h0, h1]

theorem baseExteriorFactor_at_neg_one :
    baseExteriorFactor (-1 : Circle) = 0 := by
  have hsq : baseExteriorFactor (-1 : Circle) ^ 2 = 0 := by
    rw [baseExteriorFactor_sq]
    norm_num
  exact eq_zero_of_pow_eq_zero hsq

theorem baseExteriorSymbol_factor (z : Circle) :
    baseExteriorSymbol z = (z : ℂ) * baseExteriorFactor (z ^ 2) := by
  have hz : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
  have hterm (n : ℕ) :
      baseCoeff n * (z : ℂ) ^ (1 - 2 * (n : ℤ)) =
        (z : ℂ) * (baseCoeff n * ((z ^ 2 : Circle) : ℂ) ^ (-(n : ℤ))) := by
    have hpow : ((z ^ 2 : Circle) : ℂ) ^ (-(n : ℤ)) =
        (z : ℂ) ^ (-2 * (n : ℤ)) := by
      rw [Circle.coe_pow]
      have he : -2 * (n : ℤ) = -((2 * n : ℕ) : ℤ) := by omega
      rw [he]
      simp only [zpow_neg, zpow_natCast, pow_mul]
    rw [hpow]
    have hexp : (1 : ℤ) + (-2 * (n : ℤ)) = 1 - 2 * (n : ℤ) := by ring
    have hprod : (z : ℂ) ^ (1 - 2 * (n : ℤ)) =
        (z : ℂ) * (z : ℂ) ^ (-2 * (n : ℤ)) := by
      rw [← hexp, zpow_add₀ hz]
      simp
    rw [hprod]
    ring
  calc
    baseExteriorSymbol z =
        ∑' n : ℕ, (z : ℂ) *
          (baseCoeff n * ((z ^ 2 : Circle) : ℂ) ^ (-(n : ℤ))) := by
      simp_rw [← hterm]
      rfl
    _ = (z : ℂ) * baseExteriorFactor (z ^ 2) := by
      rw [(summable_baseExteriorFactor_terms (z ^ 2)).tsum_mul_left]
      rfl

#assert_trust kernel summable_baseExteriorFactor_terms
#assert_trust kernel continuous_baseExteriorFactor
#assert_trust kernel baseExteriorFactor_sq
#assert_trust kernel baseExteriorFactor_at_neg_one
#assert_trust kernel baseExteriorSymbol_factor
#print axioms baseExteriorSymbol_factor

end NLA.Proofs.SP14
