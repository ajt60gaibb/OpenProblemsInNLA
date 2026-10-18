import NLA.Proofs.SP11.AlternatingPolynomial
import Mathlib.Order.WellFounded

/-!
# Coordinate minors on ordered basis vectors

The concrete determinant-minor construction has its intended independent
coefficients: evaluating on an increasing coordinate basis reads precisely
that subset's coefficient. This is an algebraic coefficient identity, not a
claim of non-cancellation in the recursive graph construction.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.SP11

variable {R : Type*} [CommRing R] {d r : ℕ}

/-- Two different increasing subsets of the same size omit some coordinate
of the first subset from the second. This includes the empty-shape endpoint. -/
theorem exists_coordinate_omitted {s t : CoordinateSubset d r} (hst : s ≠ t) :
    ∃ i : Fin r, ∀ j : Fin r, s.val i ≠ t.val j := by
  classical
  by_contra! h
  choose f hf using h
  have hfinj : Function.Injective f := by
    intro i j hij
    apply s.property.injective
    rw [hf i, hf j, hij]
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hfinj
  apply hst
  apply Subtype.ext
  apply (s.property.range_inj t.property).mp
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨f i, (hf i).symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨i, hi⟩ := hsurj j
    exact ⟨i, (hf i).trans (congrArg t.val hi)⟩

/-- A determinant minor evaluated on the increasing basis of another subset
is one for the matching subset and zero otherwise. -/
theorem coordinateMinorForm_basis (s t : CoordinateSubset d r) :
    coordinateMinorForm (R := R) t (fun i => Pi.single (s.val i) 1) =
      if s = t then 1 else 0 := by
  classical
  rw [coordinateMinorForm_apply]
  by_cases hst : s = t
  · subst t
    rw [if_pos rfl]
    have hm : (show Matrix (Fin r) (Fin r) R from
        fun i j => (Pi.single (s.val i) (1 : R) : CoordinateVector R d) (s.val j)) =
        (1 : Matrix (Fin r) (Fin r) R) := by
      ext i j
      simp [Pi.single_apply, Matrix.one_apply, s.property.injective.eq_iff, eq_comm]
    rw [hm, Matrix.det_one]
  · rw [if_neg hst]
    obtain ⟨i, hi⟩ := exists_coordinate_omitted hst
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    exact Pi.single_eq_of_ne (hi j).symm 1

/-- Ordered coordinate basis evaluation reads an arbitrary coefficient exactly. -/
theorem weightedMinorForm_basis (c : CoordinateSubset d r → R) (s : CoordinateSubset d r) :
    weightedMinorForm c (fun i => Pi.single (s.val i) 1) = c s := by
  classical
  rw [weightedMinorForm_apply]
  have h (t : CoordinateSubset d r) :
      Matrix.det (fun i j : Fin r => (Pi.single (s.val i) (1 : R) : CoordinateVector R d) (t.val j)) =
        if s = t then 1 else 0 := coordinateMinorForm_basis s t
  simp_rw [h]
  simp

/-- The universal polynomial form really has the advertised variable as each
ordered basis coefficient; repeated uses of a name remain the same variable. -/
theorem polynomialAlternatingForm_basis {V : Type*}
    (name : CoordinateSubset d r → V) (s : CoordinateSubset d r) :
    polynomialAlternatingForm (R := R) name (fun i => Pi.single (s.val i) 1) =
      MvPolynomial.X (name s) :=
  weightedMinorForm_basis _ _

#assert_trust kernel exists_coordinate_omitted
#assert_trust kernel coordinateMinorForm_basis
#assert_trust kernel weightedMinorForm_basis
#assert_trust kernel polynomialAlternatingForm_basis
#print axioms polynomialAlternatingForm_basis

end NLA.Proofs.SP11
