import NLA.Proofs.TR14.GL2Homogeneous
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
The exact zero-based coefficient basis of genuine homogeneous binary forms.
Every degree, including zero, is covered. No apolar or rank statement is made.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open MvPolynomial
noncomputable section

/-- The exponent pair `(d-i,i)` of the zero-based degree-`d` monomial. -/
def binaryExponent (d : ℕ) (i : Fin (d + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![d - i.val, i.val]

@[simp] theorem binaryExponent_zero (d : ℕ) (i : Fin (d + 1)) :
    binaryExponent d i 0 = d - i.val := rfl

@[simp] theorem binaryExponent_one (d : ℕ) (i : Fin (d + 1)) :
    binaryExponent d i 1 = i.val := rfl

theorem binaryExponent_degree (d : ℕ) (i : Fin (d + 1)) :
    (binaryExponent d i).degree = d := by
  have hi : i.val ≤ d := Nat.lt_succ_iff.mp i.isLt
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  simp [binaryExponent, Nat.sub_add_cancel hi]

/-- Degree-`d` exponent pairs are exactly the `d+1` zero-based indices. -/
def binaryExponentEquiv (d : ℕ) :
    Fin (d + 1) ≃ {s : Fin 2 →₀ ℕ // s.degree = d} where
  toFun i := ⟨binaryExponent d i, binaryExponent_degree d i⟩
  invFun s := ⟨s.1 1, by
    have hs : s.1 0 + s.1 1 = d := by
      simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using s.2
    omega⟩
  left_inv i := by
    apply Fin.ext
    simp
  right_inv s := by
    apply Subtype.ext
    apply Finsupp.ext
    intro k
    fin_cases k
    · have hs : s.1 0 + s.1 1 = d := by
        simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using s.2
      simp [binaryExponent]
      omega
    · simp [binaryExponent]

/-- The complete zero-based coefficient equivalence for binary forms. -/
def binaryFormEquiv (d : ℕ) : (Fin (d + 1) → ℂ) ≃ₗ[ℂ] BinaryForm d := by
  let support : Set (Fin 2 →₀ ℕ) := {s | s.degree = d}
  let E₁ : (Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin (d + 1) →₀ ℂ) :=
    (Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin (d + 1))).symm
  let E₂ : (Fin (d + 1) →₀ ℂ) ≃ₗ[ℂ] (support →₀ ℂ) :=
    Finsupp.domLCongr (binaryExponentEquiv d)
  let E₃ : (support →₀ ℂ) ≃ₗ[ℂ]
      ↥(AddMonoidAlgebra.supported ℂ ℂ support : Submodule ℂ (MvPolynomial (Fin 2) ℂ)) :=
    (AddMonoidAlgebra.supportedEquivFinsupp support).symm
  have hsub : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ d =
      (AddMonoidAlgebra.supported ℂ ℂ support : Submodule ℂ (MvPolynomial (Fin 2) ℂ)) :=
    MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 2) ℂ d
  let E₄ : ↥(AddMonoidAlgebra.supported ℂ ℂ support :
      Submodule ℂ (MvPolynomial (Fin 2) ℂ)) ≃ₗ[ℂ] BinaryForm d :=
    LinearEquiv.ofEq _ _ hsub.symm
  exact E₁.trans (E₂.trans (E₃.trans E₄))

theorem binaryFormEquiv_single_monomial (d : ℕ) (i : Fin (d + 1)) :
    binaryFormEquiv d (Pi.single i 1) = binaryMonomial d i := by
  apply Subtype.ext
  simp [binaryFormEquiv, binaryExponentEquiv, binaryMonomial,
    AddMonoidAlgebra.supportedEquivFinsupp, binaryExponent]
  change MvPolynomial.monomial (binaryExponent d i) 1 =
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ^ (d - i.val) *
      (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) ^ i.val
  rw [MvPolynomial.monomial_fin_two]
  simp

/-- The zero-based monomials span every genuine homogeneous binary form. -/
theorem binaryFormEquiv_eq_sum (d : ℕ) (g : Fin (d + 1) → ℂ) :
    binaryFormEquiv d g = ∑ i : Fin (d + 1), g i • binaryMonomial d i := by
  classical
  have hdecomp : g = ∑ i : Fin (d + 1), g i • Pi.single i (1 : ℂ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hdecomp]
  rw [map_sum]
  simp_rw [map_smul, binaryFormEquiv_single_monomial]

/-- Every coefficient is recovered from its homogeneous form. -/
theorem binaryFormEquiv_symm_monomial (d : ℕ) (i : Fin (d + 1)) :
    (binaryFormEquiv d).symm (binaryMonomial d i) = Pi.single i 1 := by
  rw [← binaryFormEquiv_single_monomial]
  exact (binaryFormEquiv d).symm_apply_apply _

/-- Multiplying two zero-based monomials adds their indices exactly. -/
theorem binaryMonomial_mul {d e : ℕ} (i : Fin (d + 1)) (j : Fin (e + 1)) :
    binaryMul (binaryMonomial d i) (binaryMonomial e j) =
      binaryMonomial (d + e) ⟨i.val + j.val, by
        have hi := i.isLt
        have hj := j.isLt
        omega⟩ := by
  apply Subtype.ext
  change ((MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ^ (d - i.val) *
      MvPolynomial.X 1 ^ i.val) *
    (MvPolynomial.X 0 ^ (e - j.val) * MvPolynomial.X 1 ^ j.val) =
    MvPolynomial.X 0 ^ ((d + e) - (i.val + j.val)) *
      MvPolynomial.X 1 ^ (i.val + j.val)
  have hexp : (d + e) - (i.val + j.val) = (d - i.val) + (e - j.val) := by
    have hi := i.isLt
    have hj := j.isLt
    omega
  rw [hexp, pow_add, pow_add]
  ring

#assert_trust kernel binaryExponentEquiv
#assert_trust kernel binaryFormEquiv
#assert_trust kernel binaryFormEquiv_single_monomial
#assert_trust kernel binaryFormEquiv_eq_sum
#assert_trust kernel binaryMonomial_mul
#print axioms binaryFormEquiv

end
end NLA.Proofs.TR14
