import NLA.Proofs.TR14.NormalizedQuotient
import NLA.Proofs.TR14.GL2HankelMode

/-!
The exact affine mode polynomial and its quotient image, and the all-moment
multilinear pairing for the frozen zero-based Hankel tensor. This module makes
no CRT, Frobenius, width, or full TR-14 Target claim.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open NLA.Statements.TR14 Polynomial
open scoped BigOperators Polynomial
noncomputable section

/-- The genuine zero-based affine polynomial of a degree-`q` mode vector. -/
def affineModePolynomial (q : ℕ) (v : Fin (q + 1) → ℂ) : Polynomial ℂ :=
  ∑ i : Fin (q + 1), Polynomial.C (v i) * Polynomial.X ^ i.val

/-- The mode polynomial evaluated at the quotient root. -/
def quotientMode (g : Polynomial ℂ) (q : ℕ)
    (v : Fin (q + 1) → ℂ) : AdjoinRoot g :=
  ∑ i : Fin (q + 1), (v i) • (AdjoinRoot.root g) ^ i.val

/-- The coordinate sum is exactly the canonical polynomial's quotient image. -/
theorem quotientMode_eq_aeval (g : Polynomial ℂ) (q : ℕ)
    (v : Fin (q + 1) → ℂ) :
    quotientMode g q v =
      Polynomial.aeval (AdjoinRoot.root g) (affineModePolynomial q v) := by
  simp [quotientMode, affineModePolynomial, Algebra.smul_def]

/-- The quotient-root powers multiply to the exact frozen zero-based
multi-index exponent, including empty mode products. -/
private theorem quotient_root_mode_product (g : Polynomial ℂ) {m q : ℕ}
    (i : Fin m → Fin (q + 1)) :
    (∏ k : Fin m, (AdjoinRoot.root g) ^ (i k).val) =
      (AdjoinRoot.root g) ^ (HankelIndex i).val := by
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

/-- Every full moment through degree `m*q` evaluates the multilinear
quotient-mode product to the exact zero-based Hankel pairing. -/
theorem quotient_mode_pairing_of_all_moments {m q : ℕ}
    (h : Fin (m * q + 1) → ℂ) (g : Polynomial ℂ)
    (Λ : AdjoinRoot g →ₗ[ℂ] ℂ)
    (hall : ∀ j : Fin (m * q + 1),
      Λ ((AdjoinRoot.root g) ^ j.val) = h j)
    (u : Fin m → Fin (q + 1) → ℂ) :
    Λ (∏ k : Fin m, quotientMode g q (u k)) =
      ∑ i : Fin m → Fin (q + 1),
        Hankel h i * ∏ k : Fin m, u k (i k) := by
  simp only [quotientMode]
  rw [Fintype.prod_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.prod_smul]
  rw [quotient_root_mode_product g i, map_smul, hall (HankelIndex i)]
  simp only [Hankel, smul_eq_mul]
  ring

/-- The audited monic all-moment quotient supplies the exact premise without
any extra assumptions on quotient reduction or the mode degree. -/
theorem quotientMomentFunctional_mode_pairing {m q : ℕ}
    (h : Fin (m * q + 1) → ℂ) (g : Polynomial ℂ)
    (hg : g.Monic) (hrD : g.natDegree ≤ m * q)
    (hrec : MonicMomentRecurrence h g)
    (u : Fin m → Fin (q + 1) → ℂ) :
    quotientMomentFunctional h g hg hrD
      (∏ k : Fin m, quotientMode g q (u k)) =
      ∑ i : Fin m → Fin (q + 1),
        Hankel h i * ∏ k : Fin m, u k (i k) := by
  exact quotient_mode_pairing_of_all_moments h g
    (quotientMomentFunctional h g hg hrD)
    (quotientMomentFunctional_all h g hg hrD hrec) u

/-- The exact frozen apolar equations imply the same multilinear quotient
pairing through the already audited monic recurrence. -/
theorem quotientMomentFunctional_mode_pairing_of_apolar {m q : ℕ}
    (h : Fin (m * q + 1) → ℂ) (g : Polynomial ℂ)
    (hg : g.Monic) (hrD : g.natDegree ≤ m * q)
    (hAp : IsApolar h g.natDegree hrD
      (fun i : Fin (g.natDegree + 1) => g.coeff i.val))
    (u : Fin m → Fin (q + 1) → ℂ) :
    quotientMomentFunctional h g hg hrD
      (∏ k : Fin m, quotientMode g q (u k)) =
      ∑ i : Fin m → Fin (q + 1),
        Hankel h i * ∏ k : Fin m, u k (i k) := by
  exact quotientMomentFunctional_mode_pairing h g hg hrD
    (monicMomentRecurrence_of_apolar h g hg hrD hAp) u

#assert_trust kernel affineModePolynomial
#assert_trust kernel quotientMode
#assert_trust kernel quotientMode_eq_aeval
#assert_trust kernel quotient_root_mode_product
#assert_trust kernel quotient_mode_pairing_of_all_moments
#assert_trust kernel quotientMomentFunctional_mode_pairing
#assert_trust kernel quotientMomentFunctional_mode_pairing_of_apolar
#print axioms quotientMomentFunctional_mode_pairing_of_apolar

end
end NLA.Proofs.TR14
