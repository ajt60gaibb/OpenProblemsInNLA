import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Matrix.DotProduct
import LeanCert.Tactic.Verification

/-!
# Alternating contraction for the SP-11 representation construction

This is the algebraic orthogonality step of the uniform LSS construction.
It proves no graph faithfulness or noncancellation theorem. The output slot
is placed first; moving it to the last slot changes only the global sign.
-/

set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.SP11

variable {R : Type*} [CommRing R] {d k : ℕ}

abbrev CoordinateVector (R : Type*) (d : ℕ) := Fin d → R

/-- Evaluation of an alternating form with all but its first slot fixed. -/
def contractionFunctional
    (a : (CoordinateVector R d) [⋀^Fin (k + 1)]→ₗ[R] R)
    (w : Fin k → CoordinateVector R d) : CoordinateVector R d →ₗ[R] R where
  toFun y := a (Matrix.vecCons y w)
  map_add' x y := a.map_vecCons_add w x y
  map_smul' c x := a.map_vecCons_smul w c x

/-- The vector representing the contraction in the standard bilinear pairing. -/
def alternatingContraction
    (a : (CoordinateVector R d) [⋀^Fin (k + 1)]→ₗ[R] R)
    (w : Fin k → CoordinateVector R d) : CoordinateVector R d :=
  fun i => contractionFunctional a w (Pi.single i 1)

/-- Contracting and then taking a dot product evaluates the original form. -/
theorem alternatingContraction_dotProduct
    (a : (CoordinateVector R d) [⋀^Fin (k + 1)]→ₗ[R] R)
    (w : Fin k → CoordinateVector R d) (y : CoordinateVector R d) :
    alternatingContraction a w ⬝ᵥ y = a (Matrix.vecCons y w) := by
  let L := contractionFunctional a w
  have hy : y = ∑ i : Fin d, y i • Pi.single i (1 : R) := by
    ext j
    simp [Pi.single_apply]
  calc
    alternatingContraction a w ⬝ᵥ y = ∑ i : Fin d, y i * L (Pi.single i 1) := by
      simp only [dotProduct, alternatingContraction, L, mul_comm]
    _ = L (∑ i : Fin d, y i • Pi.single i 1) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = L y := congrArg L hy.symm
    _ = a (Matrix.vecCons y w) := rfl

/-- Every input vector is exactly orthogonal to the contraction. -/
theorem alternatingContraction_orthogonal
    (a : (CoordinateVector R d) [⋀^Fin (k + 1)]→ₗ[R] R)
    (w : Fin k → CoordinateVector R d) (s : Fin k) :
    alternatingContraction a w ⬝ᵥ w s = 0 := by
  rw [alternatingContraction_dotProduct]
  apply a.map_eq_zero_of_eq (i := 0) (j := s.succ)
  · simp
  · exact s.succ_ne_zero.symm

#assert_trust kernel alternatingContraction_dotProduct
#assert_trust kernel alternatingContraction_orthogonal
#print axioms alternatingContraction_dotProduct
#print axioms alternatingContraction_orthogonal

end NLA.Proofs.SP11
