import NLA.Proofs.SP11.AlternatingContraction
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Concrete polynomial alternating tensors

An increasing coordinate tuple indexes one determinant minor. Weighting these
minors by independent variables supplies actual polynomial alternating forms,
with one shared coefficient family per vertex rather than per tree occurrence.
This module does not prove the graph-specific noncancellation claim.
-/

set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.SP11

/-- Increasing coordinate tuples, one for each coordinate subset of a fixed size. -/
abbrev CoordinateSubset (d r : ℕ) := {s : Fin r → Fin d // StrictMono s}

noncomputable instance coordinateSubsetFintype (d r : ℕ) :
    Fintype (CoordinateSubset d r) := Fintype.ofFinite _

variable {R : Type*} [CommRing R] {d r : ℕ}

/-- Restriction of a vector to a selected ordered coordinate set. -/
def selectedCoordinates (s : CoordinateSubset d r) :
    CoordinateVector R d →ₗ[R] (Fin r → R) where
  toFun x := x ∘ s.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coordinate determinant minor, as an actual alternating multilinear form. -/
def coordinateMinorForm (s : CoordinateSubset d r) :
    (CoordinateVector R d) [⋀^Fin r]→ₗ[R] R :=
  Matrix.detRowAlternating.compLinearMap (selectedCoordinates s)

@[simp] theorem coordinateMinorForm_apply (s : CoordinateSubset d r)
    (w : Fin r → CoordinateVector R d) :
    coordinateMinorForm s w = Matrix.det (fun i j => w i (s.val j)) := rfl

/-- Arbitrary concrete coefficients on increasing tuples define an alternating form. -/
noncomputable def weightedMinorForm (c : CoordinateSubset d r → R) :
    (CoordinateVector R d) [⋀^Fin r]→ₗ[R] R :=
  ∑ s, c s • coordinateMinorForm s

@[simp] theorem weightedMinorForm_apply (c : CoordinateSubset d r → R)
    (w : Fin r → CoordinateVector R d) :
    weightedMinorForm c w = ∑ s, c s * Matrix.det (fun i j => w i (s.val j)) := by
  classical
  have hs (S : Finset (CoordinateSubset d r)) :
      (∑ s ∈ S, c s • coordinateMinorForm s) w =
        ∑ s ∈ S, c s * Matrix.det (fun i j => w i (s.val j)) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert s S hs ih => simp [Finset.sum_insert, hs, AlternatingMap.add_apply, ih]
  exact hs Finset.univ

/-- A universal polynomial alternating form with explicitly named coefficients.
Using the same `name` at every recursive occurrence shares the node variables. -/
noncomputable def polynomialAlternatingForm {V : Type*}
    (name : CoordinateSubset d r → V) :
    (CoordinateVector (MvPolynomial V R) d) [⋀^Fin r]→ₗ[MvPolynomial V R]
      MvPolynomial V R :=
  weightedMinorForm (fun s => MvPolynomial.X (name s))

@[simp] theorem polynomialAlternatingForm_apply {V : Type*}
    (name : CoordinateSubset d r → V)
    (w : Fin r → CoordinateVector (MvPolynomial V R) d) :
    polynomialAlternatingForm name w =
      ∑ s, MvPolynomial.X (name s) * Matrix.det (fun i j => w i (s.val j)) :=
  weightedMinorForm_apply _ _

/-- The concrete polynomial contraction has exact orthogonality to each input. -/
theorem polynomialAlternatingForm_contraction_orthogonal {V : Type*} {k : ℕ}
    (name : CoordinateSubset d (k + 1) → V)
    (w : Fin k → CoordinateVector (MvPolynomial V R) d) (s : Fin k) :
    alternatingContraction (polynomialAlternatingForm name) w ⬝ᵥ w s = 0 :=
  alternatingContraction_orthogonal _ _ _

#assert_trust kernel weightedMinorForm_apply
#assert_trust kernel polynomialAlternatingForm_apply
#assert_trust kernel polynomialAlternatingForm_contraction_orthogonal
#print axioms polynomialAlternatingForm_contraction_orthogonal

end NLA.Proofs.SP11
