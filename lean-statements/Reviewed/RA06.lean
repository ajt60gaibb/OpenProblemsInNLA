/- Frozen statement boundary. Changes reopen independent review. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! RA-06: the full negative answer for the prescribed ordinary-sensitivity
independent row sampler. See docs/lean/statements/RA-06/NUMERICAL_TARGETS.md.
This states the result; it does not prove the counterexample theorem. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.ReviewedStatements.RA06

/-- The exact real row action of a rectangular matrix. -/
def RowValue {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (i : Fin n) (x : Fin d → ℝ) : ℝ :=
  ∑ j, A i j * x j

/-- The original full-column-rank promise, expressed as injectivity. -/
def FullColumnRank {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) : Prop :=
  ∀ x : Fin d → ℝ, (∀ i, RowValue A i x = 0) → ∀ j, x j = 0

/-- The exact pth power of the ℓ_p norm of `A x`, for a real exponent. -/
noncomputable def InputEnergy {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, Real.rpow |RowValue A i x| p

/-- Ordinary row sensitivity. The denominator is positive for nonzero `x`
when the quantified matrix has full column rank. No augmented score occurs. -/
noncomputable def Sensitivity {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (i : Fin n) : ℝ :=
  sSup {y : ℝ | ∃ x : Fin d → ℝ,
    (∃ j, x j ≠ 0) ∧
    y = Real.rpow |RowValue A i x| p / InputEnergy A p x}

noncomputable def TotalSensitivity {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p : ℝ) : ℝ :=
  ∑ i, Sensitivity A p i

/-- The exact floor and saturation rule from RA-06. -/
noncomputable def RetentionProbability {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p α : ℝ) (i : Fin n) : ℝ :=
  min 1 ((1 : ℝ) / (n : ℝ) + Sensitivity A p i / α)

/-- Probability of one Boolean retention vector under independent Bernoulli
draws with the prescribed possibly unequal probabilities. -/
noncomputable def OutcomeWeight {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p α : ℝ)
    (kept : Fin n → Bool) : ℝ :=
  ∏ i : Fin n,
    if kept i = true then RetentionProbability A p α i
    else 1 - RetentionProbability A p α i

/-- Exactly the ℓ_p norm power after retained row `i` is rescaled by
`q_i^(-1/p)`; for admissible inputs `q_i>0`, so its pth-power weight is `1/q_i`. -/
noncomputable def SampledEnergy {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p α : ℝ)
    (kept : Fin n → Bool) (x : Fin d → ℝ) : ℝ :=
  ∑ i : Fin n,
    if kept i = true then
      Real.rpow |RowValue A i x| p / RetentionProbability A p α i
    else 0

/-- One sampled matrix preserves both norm-power bounds simultaneously for
every real test vector. -/
def Embedding {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p α ε : ℝ) (kept : Fin n → Bool) : Prop :=
  ∀ x : Fin d → ℝ,
    (1 - ε) * InputEnergy A p x ≤ SampledEnergy A p α kept x ∧
      SampledEnergy A p α kept x ≤ (1 + ε) * InputEnergy A p x

/-- Exact finite probability of the simultaneous all-vector event. -/
noncomputable def SuccessProbability {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p α ε : ℝ) : ℝ := by
  classical
  exact ∑ kept : Fin n → Bool,
    if Embedding A p α ε kept then OutcomeWeight A p α kept else 0

/-- The expected number of retained rows is the sum of the marginals. -/
noncomputable def ExpectedSize {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p α : ℝ) : ℝ :=
  ∑ i, RetentionProbability A p α i

/-- One pair of constants depending only on the fixed real exponent `p`
must work for every full-rank matrix, both tolerances, and one shared `α`.
The logarithmic exponent is an arbitrary positive real constant. -/
def OriginalPositiveClaim (p : ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (n d : ℕ), 0 < n → 0 < d →
      ∀ A : Matrix (Fin n) (Fin d) ℝ, FullColumnRank A →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 / 2 → 0 < δ → δ < 1 / 2 →
        ∃ α : ℝ, 0 < α ∧
          ExpectedSize A p α ≤
            C * Real.rpow ε (-2) * (TotalSensitivity A p + (d : ℝ)) *
              Real.rpow (Real.log (2 * (n : ℝ) * (d : ℝ) / (ε * δ))) c ∧
          1 - δ ≤ SuccessProbability A p α ε

/-- The resolved target negates the complete original assertion for every
fixed real exponent strictly greater than two. -/
def Target : Prop :=
  ∀ p : ℝ, 2 < p → ¬ OriginalPositiveClaim p

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.RA06
