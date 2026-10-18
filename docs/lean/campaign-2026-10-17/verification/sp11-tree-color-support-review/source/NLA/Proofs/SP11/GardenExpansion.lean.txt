import NLA.Proofs.SP11.PolynomialLSS
import NLA.Proofs.SP11.MinorBasis
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.Data.Finset.Sort

/-!
# Exact coordinate expansion of the shared-variable LSS construction

These identities keep every occurrence of a vertex's actual alternating form.
They do not introduce independent coefficients for repeated subtree occurrences
and do not assert Hall's non-cancellation theorem.
-/

set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.SP11

variable {R : Type*} [CommRing R] {d r k : ℕ}

/-- An alternating form expanded in the coordinate basis, with one color per slot. -/
theorem alternatingForm_coordinateExpansion
    (a : (CoordinateVector R d) [⋀^Fin r]→ₗ[R] R)
    (w : Fin r → CoordinateVector R d) :
    a w = ∑ c : Fin r → Fin d,
      (∏ s, w s (c s)) * a (fun s => Pi.single (c s) 1) := by
  classical
  have hw : w = fun s => ∑ q : Fin d, w s q • Pi.single q (1 : R) := by
    funext s
    ext q
    simp [Pi.single_apply]
  calc
    a w = a (fun s => ∑ q : Fin d, w s q • Pi.single q (1 : R)) := congrArg a hw
    _ = ∑ c : Fin r → Fin d,
        a (fun s => w s (c s) • Pi.single (c s) 1) :=
      a.toMultilinearMap.map_sum (fun s q => w s q • Pi.single q 1)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      simpa only [smul_eq_mul] using
        a.map_smul_univ (fun s => w s (c s)) (fun s => Pi.single (c s) 1)

/-- The actual contraction expands over the colors on the incoming conduits.
The fixed output coordinate is not summed a second time. -/
theorem alternatingContraction_coordinateExpansion
    (a : (CoordinateVector R d) [⋀^Fin (k + 1)]→ₗ[R] R)
    (w : Fin k → CoordinateVector R d) (q : Fin d) :
    alternatingContraction a w q = ∑ c : Fin k → Fin d,
      (∏ s, w s (c s)) *
        a (Matrix.vecCons (Pi.single q 1) (fun s => Pi.single (c s) 1)) := by
  exact alternatingForm_coordinateExpansion (a.curryLeft (Pi.single q 1)) w

/-- A vertex's basis coefficient, with its output coordinate placed first. -/
noncomputable def vertexCoefficient {n d : ℕ} (G : SimpleGraph (Fin n))
    (j : Fin n) (q : Fin d) (c : Fin (priorNonneighbors G j).length → Fin d) :
    MvPolynomial (LSSVariable G d) ℝ :=
  universalVertexForms G j
    (Matrix.vecCons (Pi.single q 1) (fun s => Pi.single (c s) 1))

/-- One exact finite expansion step of the concrete shared-variable polynomial
recursion. All repeated occurrences use the same `vertexCoefficient`. -/
theorem polynomialLSS_coordinateExpansion {n d : ℕ}
    (G : SimpleGraph (Fin n)) (j : Fin n) (q : Fin d) :
    polynomialLSS G d j q =
      ∑ c : Fin (priorNonneighbors G j).length → Fin d,
        (∏ s, polynomialLSS G d (priorVertex G j s) (c s)) *
          vertexCoefficient G j q c := by
  change uniformLSS G (universalVertexForms G) j q = _
  rw [uniformLSS_eq]
  exact alternatingContraction_coordinateExpansion _ _ _

/-- Permuting an increasing coordinate tuple changes only the alternating
sign. This identity does not require occurrence variables to be independent. -/
theorem alternatingForm_basis_perm
    (a : (CoordinateVector R d) [⋀^Fin r]→ₗ[R] R)
    (s : CoordinateSubset d r) (p : Equiv.Perm (Fin r)) :
    a (fun i => Pi.single (s.val (p i)) 1) =
      Equiv.Perm.sign p • a (fun i => Pi.single (s.val i) 1) := by
  change a ((fun i => Pi.single (s.val i) 1) ∘ p) = _
  exact a.map_perm _ p

/-- A distinct color tuple presented as a permutation of increasing colors
contributes exactly its signed shared variable. -/
theorem polynomialAlternatingForm_basis_perm {V : Type*}
    (name : CoordinateSubset d r → V) (s : CoordinateSubset d r)
    (p : Equiv.Perm (Fin r)) :
    polynomialAlternatingForm (R := R) name (fun i => Pi.single (s.val (p i)) 1) =
      Equiv.Perm.sign p • MvPolynomial.X (name s) := by
  rw [alternatingForm_basis_perm, polynomialAlternatingForm_basis]

/-- Repeated colors make the basis coefficient identically zero, not an
additional independently selected variable. -/
theorem polynomialAlternatingForm_basis_eq_zero_of_not_injective {V : Type*}
    (name : CoordinateSubset d r → V) (c : Fin r → Fin d)
    (hc : ¬ Function.Injective c) :
    polynomialAlternatingForm (R := R) name (fun i => Pi.single (c i) 1) = 0 := by
  apply (polynomialAlternatingForm name).map_eq_zero_of_not_injective
  intro h
  exact hc (fun i j he => h (congrArg (fun q : Fin d =>
    (Pi.single q (1 : MvPolynomial V R) : CoordinateVector (MvPolynomial V R) d)) he))

#assert_trust kernel alternatingForm_coordinateExpansion
#assert_trust kernel alternatingContraction_coordinateExpansion
#assert_trust kernel polynomialLSS_coordinateExpansion
#assert_trust kernel alternatingForm_basis_perm
#assert_trust kernel polynomialAlternatingForm_basis_perm
#assert_trust kernel polynomialAlternatingForm_basis_eq_zero_of_not_injective
#print axioms polynomialLSS_coordinateExpansion
#print axioms alternatingForm_basis_perm

end NLA.Proofs.SP11
