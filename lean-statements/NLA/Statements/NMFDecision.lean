import NLA.Computation.Complexity
import Mathlib.Data.Real.Basic

/-! Shared exact rational-input grammar and real nonnegative rank-two decision
predicate for NM-03. A single Input type is used by both reviewed boundaries. -/
set_option autoImplicit false
open scoped BigOperators

namespace NLA.Statements.NMFDecision

open NLA.Computation NLA.Computation.BinaryEncoding

/-- Arbitrary rectangular rational data. Empty formats have the ordinary empty
sum convention; every positive format from the original problem is included. -/
structure Input where
  rows : ℕ
  cols : ℕ
  matrix : Matrix (Fin rows) (Fin cols) ℚ
  threshold : ℚ

def ValidInput (a : Input) : Prop :=
  (∀ i j, 0 ≤ a.matrix i j) ∧ 0 ≤ a.threshold

/-- Both dimensions, every rational entry in row-major order, then threshold. -/
def Encode (a : Input) : NLA.Computation.Word :=
  encodeNat a.rows ++ encodeNat a.cols ++
    encodeRats ((List.ofFn (fun i : Fin a.rows =>
      List.ofFn (fun j : Fin a.cols => a.matrix i j))).flatten) ++
    encodeRat a.threshold

/-- Factors range over all real nonnegative entries; zeros allow inner rank
less than two. The complete squared Frobenius error accepts exact equality. -/
def MathematicalYes (a : Input) : Prop :=
  ∃ W : Matrix (Fin a.rows) (Fin 2) ℝ,
    ∃ H : Matrix (Fin 2) (Fin a.cols) ℝ,
      (∀ i k, 0 ≤ W i k) ∧ (∀ k j, 0 ≤ H k j) ∧
      (∑ i, ∑ j, ((a.matrix i j : ℝ) - ∑ k : Fin 2, W i k * H k j) ^ 2) ≤
        (a.threshold : ℝ)

/-- One fixed ordinary binary language. Malformed or invalid words are negative. -/
def DecisionLanguage : Set NLA.Computation.Word :=
  {word | ∃ a : Input, word = Encode a ∧ ValidInput a ∧ MathematicalYes a}


end NLA.Statements.NMFDecision
