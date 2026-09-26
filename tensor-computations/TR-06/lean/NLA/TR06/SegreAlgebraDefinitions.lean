import NLA.TR06.ClosedFibers
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Adjoin.Basic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set
namespace NLA.TR06.Proposed

abbrev OrderedFactorIndex (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :=
  Fin r × ((j : Fin d) × Fin (n j))

/-- Coordinate polynomials of actual ordered pure tensors in raw factor entries. -/
def segreCoordinatePolynomial {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (iq : Fin r × TensorIndex d n) : MvPolynomial (OrderedFactorIndex d n r) ℂ :=
  ∏ j : Fin d, MvPolynomial.X (iq.1, ⟨j, iq.2 j⟩)

/-- The actual coordinate subalgebra in a polynomial domain, not the quotient
by a potentially nonradical list of point-set equations. -/
def segreSourceSubalgebra (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    Subalgebra ℂ (MvPolynomial (OrderedFactorIndex d n r) ℂ) :=
  Algebra.adjoin ℂ (Set.range (segreCoordinatePolynomial (d := d) (n := n) (r := r)))

abbrev SegreSource (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :=
  ↥(segreSourceSubalgebra d n r)

def segreCoordinate {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (iq : Fin r × TensorIndex d n) : SegreSource d n r :=
  ⟨segreCoordinatePolynomial iq, Algebra.subset_adjoin (Set.mem_range_self iq)⟩

/-- Extract the ordered tuple of actual tensor coordinates of a character. -/
def characterTuple {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (f : SegreSource d n r →ₐ[ℂ] ℂ) : Fin r → Tensor ℂ d n :=
  fun i => WithLp.toLp 2 (fun q => f (segreCoordinate (i, q)))

/-- Pullback of ambient tensor coordinates by actual summand addition. -/
def additionAlgebraHom (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    MvPolynomial (TensorIndex d n) ℂ →ₐ[ℂ] SegreSource d n r :=
  MvPolynomial.aeval (fun q => ∑ i : Fin r, segreCoordinate (i, q))

def SegreAlgebraStructureStatement : Prop :=
  ∀ (d : ℕ) (n : Fin d → ℕ) (r : ℕ),
    IsDomain (SegreSource d n r) ∧ Algebra.FiniteType ℂ (SegreSource d n r)

/-- Exact point correspondence; no scheme-fiber or analytic theorem is built
into the statement. It includes every zero summand and all finite ranks. -/
def SegreCharactersStatement : Prop :=
  ∀ (d : ℕ) (n : Fin d → ℕ) (r : ℕ), 0 < d →
    Function.Injective (characterTuple (d := d) (n := n) (r := r)) ∧
    Set.range (characterTuple (d := d) (n := n) (r := r)) = closedRankOneProduct ℂ d n r ∧
    ∀ f : SegreSource d n r →ₐ[ℂ] ℂ,
      f.comp (additionAlgebraHom d n r) =
        MvPolynomial.aeval (fun q => (∑ i, characterTuple f i) q)

#check SegreAlgebraStructureStatement
#check SegreCharactersStatement
end NLA.TR06.Proposed
