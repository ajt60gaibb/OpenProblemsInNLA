import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! FR-10: the full with-replacement Walsh restricted-isometry sampling
question. The exact source and numerical interpretation are frozen at
docs/lean/statements/FR-10/. This file states the result; it does not prove
the sampling theorem. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Statements.FR10

/-- The row and column index set is the d-dimensional vector space over F₂. -/
abbrev Index (d : ℕ) := Fin d → ZMod 2

/-- The Walsh character `(-1)^(a·b)`. Taking the integer exponent before
parity is equivalent because the base is `-1`. -/
def walshSign {d : ℕ} (a b : Index d) : ℝ :=
  (-1 : ℝ) ^ (∑ j : Fin d, (a j).val * (b j).val)

/-- Support cardinality counts exactly the nonzero real coordinates. -/
noncomputable def Sparse {d : ℕ} (k : ℕ) (x : Index d → ℝ) : Prop := by
  classical
  exact (Finset.univ.filter (fun b : Index d => x b ≠ 0)).card ≤ k

def vectorEnergy {d : ℕ} (x : Index d → ℝ) : ℝ :=
  ∑ b, (x b) ^ 2

/-- Squared norm of `√(N/m)` times the sampled normalized Walsh matrix.
The factors of `N` cancel algebraically; no square root is approximated. -/
noncomputable def sampledEnergy {d m : ℕ} (rows : Fin m → Index d)
    (x : Index d → ℝ) : ℝ :=
  (∑ i : Fin m, (∑ b : Index d, walshSign (rows i) b * x b) ^ 2) / (m : ℝ)

/-- A single ordered sample works simultaneously for every k-sparse real
vector, with both original weak distortion inequalities. -/
def RIP {d m : ℕ} (k : ℕ) (rows : Fin m → Index d) : Prop :=
  ∀ x : Index d → ℝ, Sparse k x →
    (1 / 2 : ℝ) * vectorEnergy x ≤ sampledEnergy rows x ∧
      sampledEnergy rows x ≤ (3 / 2 : ℝ) * vectorEnergy x

/-- Exact finite uniform product law on all ordered row tuples. Functions
`Fin m → Index d` include repeats and permit `m > 2^d`. The denominator is
the cardinality `(2^d)^m`, so this is the source's iid-with-replacement law. -/
noncomputable def successProbability (d m k : ℕ) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun rows : Fin m → Index d => RIP k rows)).card : ℝ) /
    (((2 ^ d) ^ m : ℕ) : ℝ)

def Qualifies (d k m : ℕ) : Prop :=
  1 ≤ m ∧ (9 / 10 : ℝ) ≤ successProbability d m k

/-- The least qualifying positive count, if the set is nonempty. The public
target below explicitly asserts membership and leastness, avoiding the
`sInf ∅ = 0` convention. -/
noncomputable def mStar (d k : ℕ) : ℕ :=
  sInf {m : ℕ | Qualifies d k m}

def IsMinimumSampleCount (d k : ℕ) : Prop :=
  Qualifies d k (mStar d k) ∧
    ∀ m : ℕ, Qualifies d k m → mStar d k ≤ m

/-- The universal sampling rate uses natural logarithms and Euler's number.
All integer factors are embedded in the reals. -/
noncomputable def Rate (d k : ℕ) : ℝ :=
  (k : ℝ) * Real.log (2 * (k : ℝ)) *
    Real.log (2 * Real.exp 1 * (((2 ^ d : ℕ) : ℝ) / (k : ℝ)))

/-- The manuscript's additional explicit numerical lower coefficient.
It is recorded separately from the original existential-constant question. -/
def ManuscriptQuantitativeBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 2 ≤ k → k ≤ 2 ^ d →
      (1 / 2000 : ℝ) * Rate d k ≤ (mStar d k : ℝ) ∧
        (mStar d k : ℝ) ≤ C * Rate d k

/-- The original full target: the minimum exists at every admissible
sparsity, `k=1` needs one row, and a single pair of positive constants
works simultaneously for all dimensions and all `2 ≤ k ≤ 2^d`. -/
def Target : Prop :=
  (∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k ≤ 2 ^ d →
    IsMinimumSampleCount d k) ∧
  (∀ d : ℕ, 1 ≤ d → mStar d 1 = 1) ∧
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 2 ≤ k → k ≤ 2 ^ d →
      c * Rate d k ≤ (mStar d k : ℝ) ∧
        (mStar d k : ℝ) ≤ C * Rate d k

#assert_statement Target
#assert_statement ManuscriptQuantitativeBound
#assert_trust kernel Target
#assert_trust kernel ManuscriptQuantitativeBound
#print axioms Target

end NLA.Statements.FR10
