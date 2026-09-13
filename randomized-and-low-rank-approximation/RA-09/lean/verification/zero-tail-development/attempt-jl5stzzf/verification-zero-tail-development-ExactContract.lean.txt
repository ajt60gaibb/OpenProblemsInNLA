/- Exact consumer of independently reviewed RA-09 contract16.
Never imported by implementation. -/
import NLA.RA09.ZeroTail
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
open Matrix
noncomputable section
namespace NLA.RA09.RootContractChecks

theorem zero_tail_closure_exact_consumer {n : ℕ} {A Ahat : RealMatrix n}
    (dA : OrderedSpectralData A) (dHat : OrderedSpectralData Ahat)
    (horder : Ahat ≤ A) (f : ℝ → ℝ) (hf : AdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hτ : dA.eigenvalues ⟨k, hk⟩ = 0)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hpremise : frobeniusSquared A - frobeniusSquared (truncation dHat k) ≤
      (1+ε) * frobeniusSquared (A-truncation dA k)) :
    A = truncation dHat k ∧ Ahat = A ∧
    frobeniusSquared (functionalCalculus f A - functionTruncation dHat f k) =
      (n-k : ℕ) * (f 0)^2 ∧
    frobeniusSquared (functionalCalculus f A - functionTruncation dA f k) =
      (n-k : ℕ) * (f 0)^2 := by
  exact zero_tail_closure_proved dA dHat horder f hf k hk hτ ε hε hpremise

#assert_trust kernel zero_tail_closure_exact_consumer
#print axioms zero_tail_closure_exact_consumer
end NLA.RA09.RootContractChecks
