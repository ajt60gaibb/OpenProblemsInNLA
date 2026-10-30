import NLA.Computation.TensorTrainApproximation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR04
open NLA.Computation.TensorTrainApproximation

/-- Restrict the actual tensor index to the two sides of the prescribed cut. -/
def splitIndex (S : Shape) (j : Cut S) (x : Index S) :
    RowIndex S j × ColIndex S j :=
  (fun i => x i.1, fun i => x i.1)

@[simp] theorem splitIndex_join (S : Shape) (j : Cut S)
    (a : RowIndex S j) (b : ColIndex S j) :
    splitIndex S j (join S j a b) = (a, b) := by
  apply Prod.ext
  · funext i
    simp [splitIndex, join, i.2]
  · funext i
    simp [splitIndex, join, Nat.not_le_of_gt i.2]

@[simp] theorem join_splitIndex (S : Shape) (j : Cut S) (x : Index S) :
    join S j (splitIndex S j x).1 (splitIndex S j x).2 = x := by
  funext i
  simp [join, splitIndex]

/-- The literal index concatenation in `Unfold` is a bijection. -/
def joinEquiv (S : Shape) (j : Cut S) :
    RowIndex S j × ColIndex S j ≃ Index S where
  toFun ab := join S j ab.1 ab.2
  invFun := splitIndex S j
  left_inv ab := splitIndex_join S j ab.1 ab.2
  right_inv := join_splitIndex S j

/-- Reshaping is the genuine linear equivalence on all tensor entries. -/
def unfoldLinearEquiv (S : Shape) (j : Cut S) :
    Tensor S ≃ₗ[ℝ] Matrix (RowIndex S j) (ColIndex S j) ℝ where
  toFun Y := Unfold S Y j
  invFun M x := M (splitIndex S j x).1 (splitIndex S j x).2
  left_inv Y := by funext x; simp [Unfold]
  right_inv M := by funext a b; simp [Unfold]
  map_add' Y Z := rfl
  map_smul' c Y := rfl

noncomputable def unfoldContinuousLinearEquiv (S : Shape) (j : Cut S) :
    Tensor S ≃L[ℝ] Matrix (RowIndex S j) (ColIndex S j) ℝ :=
  (unfoldLinearEquiv S j).toContinuousLinearEquiv

@[simp] theorem unfoldLinearEquiv_apply (S : Shape) (j : Cut S) (Y : Tensor S) :
    unfoldLinearEquiv S j Y = Unfold S Y j := rfl

@[simp] theorem unfoldContinuousLinearEquiv_apply (S : Shape) (j : Cut S)
    (Y : Tensor S) : unfoldContinuousLinearEquiv S j Y = Unfold S Y j := rfl

theorem continuous_unfold (S : Shape) (j : Cut S) :
    Continuous (fun Y : Tensor S => Unfold S Y j) :=
  (unfoldContinuousLinearEquiv S j).continuous

@[simp] theorem unfold_zero (S : Shape) (j : Cut S) :
    Unfold S 0 j = 0 := rfl

@[simp] theorem unfold_add (S : Shape) (j : Cut S) (Y Z : Tensor S) :
    Unfold S (Y + Z) j = Unfold S Y j + Unfold S Z j := rfl

@[simp] theorem unfold_smul (S : Shape) (j : Cut S) (c : ℝ) (Y : Tensor S) :
    Unfold S (c • Y) j = c • Unfold S Y j := rfl

theorem unfold_injective (S : Shape) (j : Cut S) :
    Function.Injective (fun Y : Tensor S => Unfold S Y j) :=
  (unfoldLinearEquiv S j).injective

#assert_trust kernel splitIndex_join
#assert_trust kernel join_splitIndex
#assert_trust kernel joinEquiv
#assert_trust kernel unfoldLinearEquiv
#assert_trust kernel unfoldContinuousLinearEquiv
#assert_trust kernel unfoldLinearEquiv_apply
#assert_trust kernel unfoldContinuousLinearEquiv_apply
#assert_trust kernel continuous_unfold
#assert_trust kernel unfold_zero
#assert_trust kernel unfold_add
#assert_trust kernel unfold_smul
#assert_trust kernel unfold_injective
#print axioms continuous_unfold
#print axioms unfold_injective
end NLA.Proofs.TR04
