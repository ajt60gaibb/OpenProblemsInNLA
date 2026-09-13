/- Independent literal consumer of the public theorem in actual Frobenius norms.
Separate half-line function hypotheses expose that no f(0)=0 is needed.
This is reviewer evidence only; no implementation or frozen target edit.
-/
import Solution
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Classical MatrixOrder
open NLA.RA09
noncomputable section
namespace RA09FinalReferee2

theorem original_norm_target
    (n k : ℕ) (hn : 2 ≤ n) (hkone : 1 ≤ k) (hk : k < n)
    (A Ahat : RealMatrix n) (hA : A.PosSemidef) (hAhat : Ahat.PosSemidef)
    (horder : Ahat ≤ A) (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Set.Ici 0))
    (hconc : ConcaveOn ℝ (Set.Ici 0) f)
    (hmono : MonotoneOn f (Set.Ici 0)) (hnonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (dA : OrderedSpectralData A) (dHat : OrderedSpectralData Ahat)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hpre : frobeniusNorm A ^ 2 - frobeniusNorm (truncation dHat k) ^ 2 ≤
      (1+ε) * frobeniusNorm (A - truncation dA k) ^ 2) :
    frobeniusNorm (cfc f A - functionTruncation dHat f k) ^ 2 ≤
      (1+ε) * frobeniusNorm (cfc f A - functionTruncation dA f k) ^ 2 := by
  have hp : frobeniusSquared A - frobeniusSquared (truncation dHat k) ≤
      (1+ε) * frobeniusSquared (A - truncation dA k) := by
    simpa only [frobeniusSquared_norm] using hpre
  have h := concaveFrobeniusTransferConjecture n hn k hkone hk A Ahat hA hAhat horder f
    ⟨hcont,hconc,hmono,hnonneg⟩ dA dHat ε hε hp
  simpa only [frobeniusSquared_norm, functionalCalculus] using h

#assert_trust kernel original_norm_target
#print axioms original_norm_target
end RA09FinalReferee2
