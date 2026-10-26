/-
Proposed bounded algebraic statements, before implementation or independent approval.
No theorem asserting these propositions is declared here.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology.
-/
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import LeanCert.Tactic.Verification

set_option autoImplicit false
noncomputable section
open scoped Classical
open Function Set TopologicalSpace

universe u v w

namespace NLA.TR06.Proposed

/-- The actual prime kernel of a field-valued character. -/
def characterPrime {R : Type u} {S : Type v} {K : Type w}
    [CommRing R] [CommRing S] [Field K] [Algebra R S] [Algebra R K]
    (f : S →ₐ[R] K) : PrimeSpectrum S :=
  ⟨RingHom.ker f.toRingHom, RingHom.ker_isPrime f.toRingHom⟩

/-- Local character restriction is injective wherever the denominator is nonzero.
Surjectivity of the away map is sufficient; no injectivity assertion is omitted
from a Zariski Main input, whose bijectivity supplies this weaker premise. -/
def AwayCharacterRestrictionStatement : Prop :=
  ∀ (R : Type u) (S : Type v) (K : Type w) [CommRing R] [CommRing S] [Field K]
    [Algebra R S] [Algebra R K] (A : Subalgebra R S) (r : A),
    Surjective (Localization.awayMap A.val.toRingHom r) →
    Set.InjOn (fun f : S →ₐ[R] K => f.comp A.val) {f | f r.val ≠ 0}

/-- Uniformly many field-valued characters at quasi-finite source primes.
The bound is chosen before the R-algebra action on the fixed target field K.
The set q is a finite subset, so infinite-cardinality conventions play no role. -/
def UniformQuasiFiniteCharacterBoundStatement : Prop :=
  ∀ (R : Type u) (S : Type v) (K : Type w) [CommRing R] [CommRing S] [Field K]
    [Algebra R S] [Algebra.FiniteType R S]
    [NoetherianSpace (PrimeSpectrum S)],
  ∃ B : ℕ, ∀ aK : Algebra R K, letI := aK;
    ∀ q : Finset (S →ₐ[R] K),
      (∀ f ∈ q, Algebra.QuasiFiniteAt R (characterPrime f).asIdeal) → q.card ≤ B

#check AwayCharacterRestrictionStatement
#check UniformQuasiFiniteCharacterBoundStatement
#print axioms AwayCharacterRestrictionStatement
#print axioms UniformQuasiFiniteCharacterBoundStatement

end NLA.TR06.Proposed
