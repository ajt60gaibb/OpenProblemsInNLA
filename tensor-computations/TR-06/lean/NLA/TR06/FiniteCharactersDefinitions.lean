import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.QuasiFinite.Basic

set_option autoImplicit false
noncomputable section
universe u v
namespace NLA.TR06.Proposed

/-- Finitely many actual K-valued characters force a finite-type algebra over
an algebraically closed field to be module finite, including nonreduced and
trivial algebras. No finite scheme-spectrum premise is assumed. -/
def FiniteAlgebraOfFiniteCharactersStatement : Prop :=
  ∀ (K : Type u) (A : Type v) [Field K] [IsAlgClosed K] [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A],
    Set.Finite (Set.univ : Set (A →ₐ[K] K)) → Module.Finite K A

#check FiniteAlgebraOfFiniteCharactersStatement
end NLA.TR06.Proposed
