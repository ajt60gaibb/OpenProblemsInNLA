import NLA.Proofs.TR14.MomentIndex
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Tactic

/-!
Genuine homogeneous binary forms and the explicit invertible chart substitution
used in TR-14.  This module proves only the algebraic substitution and inverse-dual
moment pairing.  It makes no claim about apolar kernels, tensor widths, or the
frozen TR-14 target.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open MvPolynomial
noncomputable section

/-- Homogeneous binary forms of exact ambient degree `d`, including zero. -/
abbrev BinaryForm (d : ℕ) :=
  ↥(MvPolynomial.homogeneousSubmodule (Fin 2) ℂ d)

private abbrev BinPoly := MvPolynomial (Fin 2) ℂ

private def x : BinPoly := X 0
private def y : BinPoly := X 1

/-- Substitution `(X,Y) ↦ (Y,X+zY)`, whose matrix has determinant `-1`. -/
def chartSubst (z : ℂ) : BinPoly →ₐ[ℂ] BinPoly :=
  MvPolynomial.aeval ![y, x + C z * y]

/-- Inverse substitution `(X,Y) ↦ (Y-zX,X)`. -/
def chartSubstInv (z : ℂ) : BinPoly →ₐ[ℂ] BinPoly :=
  MvPolynomial.aeval ![y - C z * x, x]

private theorem chartSubst_comp_inv (z : ℂ) :
    (chartSubst z).comp (chartSubstInv z) = AlgHom.id ℂ BinPoly := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [chartSubst, chartSubstInv, x, y]

private theorem chartSubstInv_comp (z : ℂ) :
    (chartSubstInv z).comp (chartSubst z) = AlgHom.id ℂ BinPoly := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [chartSubst, chartSubstInv, x, y]

private theorem chartSubst_homogeneous (z : ℂ) {d : ℕ} (P : BinaryForm d) :
    (chartSubst z P.1).IsHomogeneous d := by
  have hX : x.IsHomogeneous 1 := MvPolynomial.isHomogeneous_X (R := ℂ) (0 : Fin 2)
  have hY : y.IsHomogeneous 1 := MvPolynomial.isHomogeneous_X (R := ℂ) (1 : Fin 2)
  have hsecond : (x + C z * y).IsHomogeneous 1 := hX.add (hY.C_mul z)
  have hh : ∀ i : Fin 2, (![y, x + C z * y] i).IsHomogeneous 1 := by
    intro i
    fin_cases i
    · exact hY
    · exact hsecond
  change (MvPolynomial.aeval (![y, x + C z * y]) P.1).IsHomogeneous d
  simpa only [one_mul] using P.2.aeval (![y, x + C z * y]) hh

private theorem chartSubstInv_homogeneous (z : ℂ) {d : ℕ} (P : BinaryForm d) :
    (chartSubstInv z P.1).IsHomogeneous d := by
  have hX : x.IsHomogeneous 1 := MvPolynomial.isHomogeneous_X (R := ℂ) (0 : Fin 2)
  have hY : y.IsHomogeneous 1 := MvPolynomial.isHomogeneous_X (R := ℂ) (1 : Fin 2)
  have hfirst : (y - C z * x).IsHomogeneous 1 := hY.sub (hX.C_mul z)
  have hh : ∀ i : Fin 2, (![y - C z * x, x] i).IsHomogeneous 1 := by
    intro i
    fin_cases i
    · exact hfirst
    · exact hX
  change (MvPolynomial.aeval (![y - C z * x, x]) P.1).IsHomogeneous d
  simpa only [one_mul] using P.2.aeval (![y - C z * x, x]) hh

/-- The chart substitution restricted to every homogeneous degree. -/
def chartPhi (z : ℂ) (d : ℕ) : BinaryForm d →ₗ[ℂ] BinaryForm d where
  toFun P := ⟨chartSubst z P.1, chartSubst_homogeneous z P⟩
  map_add' P Q := Subtype.ext ((chartSubst z).map_add P.1 Q.1)
  map_smul' c P := Subtype.ext ((chartSubst z).toLinearMap.map_smul c P.1)

/-- The inverse chart substitution restricted to every homogeneous degree. -/
def chartPhiInv (z : ℂ) (d : ℕ) : BinaryForm d →ₗ[ℂ] BinaryForm d where
  toFun P := ⟨chartSubstInv z P.1, chartSubstInv_homogeneous z P⟩
  map_add' P Q := Subtype.ext ((chartSubstInv z).map_add P.1 Q.1)
  map_smul' c P := Subtype.ext ((chartSubstInv z).toLinearMap.map_smul c P.1)

/-- An actual linear equivalence, in every degree including zero. -/
def chartPhiEquiv (z : ℂ) (d : ℕ) : BinaryForm d ≃ₗ[ℂ] BinaryForm d where
  toLinearMap := chartPhi z d
  invFun := chartPhiInv z d
  left_inv P := by
    apply Subtype.ext
    exact DFunLike.congr_fun (chartSubstInv_comp z) P.1
  right_inv P := by
    apply Subtype.ext
    exact DFunLike.congr_fun (chartSubst_comp_inv z) P.1

/-- Multiplication of homogeneous forms, with the exact summed degree. -/
def binaryMul {d e : ℕ} (P : BinaryForm d) (Q : BinaryForm e) : BinaryForm (d + e) :=
  ⟨P.1 * Q.1, P.2.mul Q.2⟩

/-- The canonical zero-based basis element `X^(d-i) Y^i`. -/
def binaryMonomial (d : ℕ) (i : Fin (d + 1)) : BinaryForm d := by
  have hi : i.val ≤ d := Nat.lt_succ_iff.mp i.isLt
  have hX : (x ^ (d - i.val)).IsHomogeneous (d - i.val) := by
    simpa [x] using
      (MvPolynomial.isHomogeneous_X (R := ℂ) (0 : Fin 2)).pow (d - i.val)
  have hY : (y ^ i.val).IsHomogeneous i.val := by
    simpa [y] using
      (MvPolynomial.isHomogeneous_X (R := ℂ) (1 : Fin 2)).pow i.val
  have hprod := hX.mul hY
  rw [Nat.sub_add_cancel hi] at hprod
  exact ⟨x ^ (d - i.val) * y ^ i.val, hprod⟩

/-- The degreewise substitution respects multiplication exactly. -/
theorem chartPhi_mul (z : ℂ) {d e : ℕ} (P : BinaryForm d) (Q : BinaryForm e) :
    chartPhi z (d + e) (binaryMul P Q) =
      binaryMul (chartPhi z d P) (chartPhi z e Q) := by
  apply Subtype.ext
  exact (chartSubst z).map_mul P.1 Q.1

/-- A degree-`D` moment functional is a complex-linear dual of binary forms. -/
abbrev BinaryMoment (D : ℕ) := BinaryForm D →ₗ[ℂ] ℂ

/-- Moment coordinates in the exact basis `X^(D-j)Y^j`, without binomial factors. -/
def momentCoordinates {D : ℕ} (L : BinaryMoment D) : Fin (D + 1) → ℂ :=
  fun j => L (binaryMonomial D j)

/-- The inverse-dual action: the transformed functional evaluates the inverse
substitution, with no conjugation or binomial rescaling. -/
def chartMoment (z : ℂ) {D : ℕ} (L : BinaryMoment D) : BinaryMoment D :=
  L.comp (chartPhiEquiv z D).symm.toLinearMap

/-- The inverse-dual pairing holds for every split of the ambient degree. -/
theorem chartMoment_mul_pairing (z : ℂ) {d e : ℕ} (L : BinaryMoment (d + e))
    (P : BinaryForm d) (Q : BinaryForm e) :
    chartMoment z L (binaryMul (chartPhi z d P) (chartPhi z e Q)) =
      L (binaryMul P Q) := by
  rw [← chartPhi_mul]
  exact congrArg L ((chartPhiEquiv z (d + e)).symm_apply_apply (binaryMul P Q))

#assert_trust kernel chartPhiEquiv
#assert_trust kernel chartPhi_mul
#assert_trust kernel chartMoment_mul_pairing
#print axioms chartMoment_mul_pairing

end
end NLA.Proofs.TR14
