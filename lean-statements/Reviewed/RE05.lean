/- Frozen statement boundary. Changes reopen independent review. -/
import NLA.Computation.LinearFamilyQuery
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! RE-05: pure relative Frobenius approximation by every independent finite
linear matrix family. The concrete nonadaptive 15-copy Gaussian query program,
exact arithmetic/SVD operations and median selector are shared computation
definitions, not an opaque algorithm or query-cost parameter. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Computation.LinearFamilyQuery
open NLA.Computation.NonadaptiveMatrixQuery

namespace NLA.ReviewedStatements.RE05

/-- The actual fixed-input 99/100 event for the concrete program. -/
def Successful {n q : ℕ} (P : Basis n q) (A : Square n) (ε : ℝ) : Prop :=
  GaussianLaw {ω | frobenius A (represent P (run P A ε ω)) ≤
      (1 + ε) * optimum P A} ≥ (99 / 100 : ENNReal)

/-- Actual length of the one precommitted batch, uniformly over all Gaussian
streams, bounded by the original existential asymptotic expression. -/
def QueryBound {n q : ℕ} (P : Basis n q) (ε C : ℝ) (a b : ℕ) : Prop :=
  ∀ ω : ℕ → ℝ,
    ((batchQueries (plans P ε ω)).length : ℝ) ≤
      C * Real.sqrt (q + 1 : ℕ) * (ε⁻¹) ^ a *
        (1 + Real.log (2 + (q + 1 : ℕ)) + Real.log (1 / ε)) ^ b

/-- Original complete existential, witnessed by the same named uniform
algorithm for every input. The format uses `q+1` to encode every q≥1. -/
def OriginalClaim : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ a b : ℕ,
    ∀ (n q : ℕ), 0 < n → q + 1 ≤ n * n →
      ∀ P : Basis n q, Independent P →
        ∀ A : Square n, ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
          QueryBound P ε C a b ∧ Successful P A ε

/-- The manuscript's stronger concrete count for fifteen copies at internal
squared-accuracy parameter `ε/9`. Every random execution is charged. -/
def SourceQueryBound {n q : ℕ} (P : Basis n q) (ε : ℝ) : Prop :=
  ∀ ω : ℕ → ℝ,
    ((batchQueries (plans P ε ω)).length : ℝ) ≤
      15 * (2 * Real.sqrt ((q + 1 : ℕ) *
        baseWidth q (squaredAccuracy ε)) +
        8 * Real.log (20 * (q + 1 : ℕ)) + 1)

def SourceCompanion : Prop :=
  ∀ (n q : ℕ), 0 < n → q + 1 ≤ n * n →
    ∀ P : Basis n q, Independent P →
      ∀ A : Square n, ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        SourceQueryBound P ε ∧ Successful P A ε

/-- The benchmark is a finite-dimensional **attained** minimum, including
when the target already lies in the supplied linear family. -/
def AttainedOptimum : Prop :=
  ∀ (n q : ℕ) (P : Basis n q) (A : Square n), Independent P →
    ∃ c : Fin (q + 1) → ℝ,
      frobenius A (represent P c) = optimum P A ∧
      ∀ d : Fin (q + 1) → ℝ,
        optimum P A ≤ frobenius A (represent P d)

/-- The exact full target and source witness. Exact SVD availability is an
affirmative mathematical fact about the allowed primitive, never a hypothesis. -/
def Target : Prop :=
  SVDTotal ∧ AttainedOptimum ∧ OriginalClaim ∧ SourceCompanion

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.RE05
