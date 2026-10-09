import Mathlib
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! TR-08: the exact sharp sparsity criterion for the original random signed
column model and an independent uniformly selected column subset. The full
canonical source and pre-implementation specification are retained under
`docs/lean/statements/TR-08/`. This file states the result, not its proof. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open Filter

namespace NLA.Statements.TR08

/-- A uniformly chosen subset of prescribed cardinality. -/
abbrev FixedCardSubset (α : Type*) [DecidableEq α] (s : ℕ) :=
  {S : Finset α // S.card = s}

/-- One sample draws each column's exact-size support, pre-draws all fair
signs independently (unused signs are ignored), and draws the independent
exact-size selected column set. The finite sample space has the uniform law,
so its product coordinates have precisely the original independent laws. -/
abbrev Sample (k n s : ℕ) :=
  ((Fin n → FixedCardSubset (Fin k) s) × ((Fin k × Fin n) → Bool)) ×
    FixedCardSubset (Fin n) (k / 100)

/-- The sign on a selected location, with either Boolean value equally likely. -/
noncomputable def signedEntry {k n s : ℕ} (ω : Sample k n s)
    (i : Fin k) (j : Fin n) : ℝ :=
  if i ∈ (ω.1.1 j).val then
    (if ω.1.2 (i, j) then (1 : ℝ) else -1) / Real.sqrt (s : ℝ)
  else 0

/-- The actual selected columns, indexed by their original column labels.
This deterministic ordering-free indexing has the same singular values as
ordering the selected labels increasingly. -/
abbrev SelectedIndex {k n s : ℕ} (ω : Sample k n s) :=
  {j : Fin n // j ∈ ω.2.val}

noncomputable def selectedMatrix {k n s : ℕ} (ω : Sample k n s) :
    Matrix (Fin k) (SelectedIndex ω) ℝ :=
  fun i j => signedEntry ω i j.val

/-- The genuine finite Euclidean norm, used in both the input sphere and
output vector. -/
noncomputable def euclideanNorm {α : Type*} [Fintype α] (x : α → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

/-- Least singular value of the selected `k × (k/100)` matrix: infimum over
every real unit vector, with the ordinary Euclidean norms. -/
noncomputable def leastSingular {k n s : ℕ} (ω : Sample k n s) : ℝ :=
  sInf {y : ℝ | ∃ x : SelectedIndex ω → ℝ,
    euclideanNorm x = 1 ∧
      y = euclideanNorm (fun i : Fin k => ∑ j, selectedMatrix ω i j * x j)}

/-- Exact probability under the uniform law on all support, sign, and
selected-column choices. For the admissible dimensions below this sample
space is nonempty. No random sampling or finite enumeration is performed
when stating the proposition. -/
noncomputable def successProbability (k n s : ℕ) (a : ℝ) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun ω : Sample k n s => a ≤ leastSingular ω)).card : ℝ) /
    (Fintype.card (Sample k n s) : ℝ)

/-- Indexing by `t` starts at `k=100` and visits precisely the positive
multiples of 100. -/
def rows (t : ℕ) : ℕ := 100 * (t + 1)

/-- The fixed positive ambient-growth exponent and the full, arbitrary
integer sequences from the canonical problem. -/
def Admissible (c : ℝ) (n s : ℕ → ℕ) : Prop :=
  0 < c ∧ ∀ t : ℕ,
    Real.rpow (rows t : ℝ) (1 + c) ≤ (n t : ℝ) ∧
    1 ≤ s t ∧ s t ≤ rows t

/-- One positive lower singular-value threshold has success probability
tending to one along the complete sequence of positive multiples of 100. -/
def Successful (n s : ℕ → ℕ) : Prop :=
  ∃ a : ℝ, 0 < a ∧
    Tendsto (fun t : ℕ => successProbability (rows t) (n t) (s t) a)
      atTop (nhds 1)

/-- Exact positive lower limit of `s_k² / log k`, expressed as an eventual
positive lower bound. This handles arbitrary oscillating sequences. -/
def PositiveLowerRatio (s : ℕ → ℕ) : Prop :=
  ∃ h : ℝ, 0 < h ∧
    ∀ᶠ t : ℕ in atTop,
      h * Real.log (rows t : ℝ) ≤ ((s t : ℝ) ^ 2)

/-- The complete necessary-and-sufficient threshold, uniformly for every
fixed `c>0` and every admissible ambient and sparsity sequence. The witness
`a` may depend on the sequence, but not on dimension or random outcome. -/
def Target : Prop :=
  ∀ (c : ℝ) (n s : ℕ → ℕ), Admissible c n s →
    (Successful n s ↔ PositiveLowerRatio s)

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.Statements.TR08
