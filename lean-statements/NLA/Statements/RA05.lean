import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ENNReal.Real
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! RA-05: exact strong original-row coreset size, the resolved joint
classification, and the literal original additive proposal and negative answer.
Full specification: docs/lean/statements/RA-05/NUMERICAL_TARGETS.md. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

namespace NLA.Statements.RA05

/-- Every real Euclidean orthogonal projector of rank at most k. -/
def Projector {d : ℕ} (k : ℕ) (P : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  P.transpose = P ∧ P * P = P ∧ Matrix.rank P ≤ k

noncomputable def RowCost {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (i : Fin n) : ℝ :=
  (Real.sqrt (∑ j, (A i j - ∑ h, A i h * P h j)^2)) ^ p

noncomputable def Cost {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ i, RowCost A p P i

/-- The same nonnegative weights work simultaneously for every allowed subspace. -/
def StrongCoreset {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (k : ℕ) (ε : ℝ) (w : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∀ P : Matrix (Fin d) (Fin d) ℝ, Projector k P →
    (1 - ε) * Cost A p P ≤ ∑ i, w i * RowCost A p P i ∧
    (∑ i, w i * RowCost A p P i) ≤ (1 + ε) * Cost A p P

noncomputable def SupportSize {n : ℕ} (w : Fin n → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => w i ≠ 0)).card

/-- The all-one coreset makes the natural budget set nonempty on the domain. -/
noncomputable def MinimumSupport {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (k : ℕ) (ε : ℝ) : ℕ :=
  sInf {s : ℕ | ∃ w : Fin n → ℝ, StrongCoreset A p k ε w ∧ SupportSize w ≤ s}

/-- Extended supremum over all finite dimensions and all real data matrices. -/
noncomputable def WorstSupport (p : ℝ) (k : ℕ) (ε : ℝ) : ENNReal :=
  sSup {s : ENNReal | ∃ n d : ℕ, k < d ∧
    ∃ A : Matrix (Fin n) (Fin d) ℝ, s = (MinimumSupport A p k ε : ENNReal)}

def EvenPower (p : ℝ) : Prop := ∃ s : ℕ, 2 ≤ s ∧ p = 2 * (s : ℝ)

noncomputable def LogScale (k : ℕ) (ε : ℝ) : ℝ := Real.log (2 * (k : ℝ) / ε)

noncomputable def Rate (p : ℝ) (k : ℕ) (ε : ℝ) : ℝ := by
  classical
  exact if EvenPower p then
    min ((k : ℝ) ^ (p / 2) / ε^2)
      ((k : ℝ) ^ ((p + 1) / 2) / ε + (k : ℝ) ^ (p / 2 - 1) / ε^2)
  else (k : ℝ) ^ (p / 2) / ε^2

noncomputable def LowerLogLoss (p : ℝ) : ℝ := by
  classical
  exact if EvenPower p then 0 else 5 * p / 2 + 3

/-- The complete resolved joint classification, with explicit source log losses. -/
def Classification : Prop :=
  ∀ p : ℝ, 2 < p → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ENNReal.ofReal (c * Rate p k ε / LogScale k ε ^ LowerLogLoss p) ≤
        WorstSupport p k ε ∧
      WorstSupport p k ε ≤
        ENNReal.ofReal (C * Rate p k ε * LogScale k ε ^ (p + 5))

/-- The original displayed additive proposal at one fixed real p. -/
def AdditiveProposal (p : ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ n d k : ℕ, 1 ≤ k → k < d → ∀ A : Matrix (Fin n) (Fin d) ℝ,
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ w : Fin n → ℝ,
        StrongCoreset A p k ε w ∧
        (SupportSize w : ℝ) ≤
          C * ((k : ℝ) ^ (p / 2) / ε + (k : ℝ) / ε^2) * LogScale k ε ^ c

/-- Retained literally even though the credited resolution answers it negatively. -/
def OriginalAdditiveConjecture : Prop := ∀ p : ℝ, 2 < p → AdditiveProposal p

def NegativeAnswer : Prop := ∀ p : ℝ, 2 < p → ¬ AdditiveProposal p

/-- The resolved answers to both parts of the full original question. -/
def Target : Prop := Classification ∧ NegativeAnswer

#assert_statement Classification
#assert_statement OriginalAdditiveConjecture
#assert_statement NegativeAnswer
#assert_statement Target
#assert_trust kernel Classification
#assert_trust kernel OriginalAdditiveConjecture
#assert_trust kernel NegativeAnswer
#assert_trust kernel Target
#print axioms Target

end NLA.Statements.RA05
