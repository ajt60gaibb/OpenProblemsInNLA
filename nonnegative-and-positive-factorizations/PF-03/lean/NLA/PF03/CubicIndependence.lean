/-
Original mathematics and seed: Sidney Holden, Flatiron Institute,
Simons Foundation. Formalization: George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology; Codex assistance.

The minimal polynomial is proved, not declared as a field assumption. Its
degree gives the full rational independence needed for arbitrary rational rays.
-/
import NLA.PF03.RootCertificate
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic.NormNum.Irrational

set_option autoImplicit false
open scoped BigOperators
open Polynomial
noncomputable section
namespace NLA.PF03

lemma alpha_irrational : Irrational alpha := by
  norm_num [alpha]

lemma alpha_polynomial_irreducible : Irreducible ((X : ℚ[X]) ^ 3 - C 2) := by
  apply (X_pow_sub_C_irreducible_iff_of_prime (by norm_num : Nat.Prime 3)).2
  intro b hb
  have hb' : (b : ℝ) ^ 3 = 2 := by exact_mod_cast hb
  have hab : alpha = (b : ℝ) :=
    (show Odd (3 : ℕ) by decide).pow_injective (alpha_certificate.1.trans hb'.symm)
  exact alpha_irrational.ne_rat b hab

lemma alpha_minpoly : minpoly ℚ alpha = (X : ℚ[X]) ^ 3 - C 2 := by
  symm
  apply minpoly.eq_of_irreducible_of_monic alpha_polynomial_irreducible
  · simp [alpha_certificate.1]
  · exact monic_X_pow_sub_C 2 (by decide)

lemma alpha_powers_independent :
    LinearIndependent ℚ (fun i : Fin 3 => alpha ^ (i : ℕ)) := by
  have hd : (minpoly ℚ alpha).natDegree = 3 := by
    rw [alpha_minpoly, natDegree_X_pow_sub_C]
  have hi := linearIndependent_pow (K := ℚ) alpha
  rw [hd] at hi
  exact hi

theorem cubic_eval_injective (a b c : ℚ) :
    (a : ℝ) + (b : ℝ) * alpha + (c : ℝ) * alpha ^ 2 = 0 ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    have hs : ∑ i : Fin 3, (![a, b, c] i) • alpha ^ (i : ℕ) = 0 := by
      simpa [Fin.sum_univ_succ, Algebra.smul_def, add_assoc] using h
    have hz := (Fintype.linearIndependent_iff.mp alpha_powers_independent) ![a, b, c] hs
    exact ⟨by simpa using hz 0, by simpa using hz 1, by simpa using hz 2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp

#print axioms cubic_eval_injective
#assert_trust kernel cubic_eval_injective

end NLA.PF03
