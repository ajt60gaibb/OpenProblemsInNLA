import NLA.Computation.FiniteMachine
import NLA.Computation.BinaryEncoding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation

/-! Constant-free finite rounded arithmetic with actual register reuse and
static error coordinates, followed by a concrete integer-polynomial encoding.
Exact specification: docs/lean/statements/AA-01/NUMERICAL_TARGETS.md.
The rounded tree and the ordinary binary decision machine are distinct models. -/
set_option autoImplicit false

open scoped BigOperators

namespace NLA.Computation.RoundedTree

inductive BinaryOp where
  | add
  | subtract
  | multiply

def BinaryOp.apply (op : BinaryOp) (a b : ℝ) : ℝ :=
  match op with
  | .add => a + b
  | .subtract => a - b
  | .multiply => a * b

/-- r is exactly the number of available numerical registers. No constructor
contains a real literal, an arbitrary real function, an oracle or a loop.
New numerical values are appended; old registers remain available unchanged. -/
inductive Program : ℕ → Type where
  | ret {r : ℕ} (i : Fin r) : Program r
  | negate {r : ℕ} (i : Fin r) (next : Program (r + 1)) : Program r
  | rounded {r : ℕ} (op : BinaryOp) (i j : Fin r)
      (next : Program (r + 1)) : Program r
  | compare {r : ℕ} (i j : Fin r)
      (less equal greater : Program r) : Program r

/-- Every rounded node in every branch has a coordinate, whether executed or not. -/
def Program.roundedCount {r : ℕ} : Program r → ℕ
  | .ret _ => 0
  | .negate _ next => next.roundedCount
  | .rounded _ _ _ next => next.roundedCount + 1
  | .compare _ _ less equal greater =>
      less.roundedCount + equal.roundedCount + greater.roundedCount

/-- Explicit contiguous projection of a finite error vector; no out-of-range
read or default error value exists. -/
def errorSlice {total : ℕ} (δ : Fin total → ℝ)
    (offset length : ℕ) (h : offset + length ≤ total) : Fin length → ℝ :=
  fun j => δ ⟨offset + j.val, by have hj := j.isLt; omega⟩

/-- Structural finite execution. Comparison reads actual current values;
all selected error coordinates are fixed by syntax, not execution length.
Fin.snoc preserves all old registers and appends one new value at the end. -/
noncomputable def Program.evaluate {r : ℕ} (P : Program r)
    (ρ : Fin r → ℝ) (δ : Fin P.roundedCount → ℝ) : ℝ := by
  classical
  exact match P with
  | .ret i => ρ i
  | .negate i next => next.evaluate (Fin.snoc ρ (-ρ i)) δ
  | .rounded op i j next =>
      next.evaluate (Fin.snoc ρ (op.apply (ρ i) (ρ j) * (1 + δ ⟨0, by simp [Program.roundedCount]⟩)))
        (fun j => δ j.succ)
  | .compare i j less equal greater =>
      if ρ i < ρ j then
        less.evaluate ρ (errorSlice δ 0 less.roundedCount (by simp only [Program.roundedCount]; omega))
      else if ρ i = ρ j then
        equal.evaluate ρ (errorSlice δ less.roundedCount equal.roundedCount
          (by simp only [Program.roundedCount]; omega))
      else
        greater.evaluate ρ
          (errorSlice δ (less.roundedCount + equal.roundedCount) greater.roundedCount
            (by simp [Program.roundedCount]))

/-- Literal constant-free semantics cannot output anything without any input. -/
theorem no_program_zero (P : Program 0) : False := by
  cases P with
  | ret i => exact Fin.elim0 i
  | negate i _ => exact Fin.elim0 i
  | rounded _ i _ _ => exact Fin.elim0 i
  | compare i _ _ _ _ => exact Fin.elim0 i

/-- One finite integer-coefficient monomial occurrence. Duplicate exponents
and zero coefficients are permitted in a coefficient list. -/
structure Term (n : ℕ) where
  coefficient : ℤ
  exponent : Fin n → ℕ

structure PolynomialInput where
  n : ℕ
  terms : List (Term n)

/-- Exact ordinary polynomial value, summing all list occurrences. The library
natural power convention includes x^0=1 and the empty product is one. -/
def PolynomialValue (a : PolynomialInput) (x : Fin a.n → ℝ) : ℝ :=
  (a.terms.map (fun t => (t.coefficient : ℝ) * ∏ i, x i ^ t.exponent i)).sum

def ValidInput (a : PolynomialInput) : Prop :=
  PolynomialValue a (fun _ => 0) = 0

def encodeTerm {n : ℕ} (t : Term n) : Word :=
  BinaryEncoding.encodeInt t.coefficient ++
    (List.ofFn t.exponent).flatMap BinaryEncoding.encodeNat

/-- Dimension, list length, then each signed coefficient and every exponent
in coordinate order. Polynomial coefficients are not real evaluator inputs. -/
def encodePolynomial (a : PolynomialInput) : Word :=
  BinaryEncoding.encodeNat a.n ++ BinaryEncoding.encodeNat a.terms.length ++
    a.terms.flatMap encodeTerm

/-- The same finite tree precedes every requested accuracy. The error bound
is uniform in the complete real input and in every independent error choice,
including errors assigned to branches that are not executed. -/
def Accurate (a : PolynomialInput) (P : Program a.n) : Prop :=
  (∀ x : Fin a.n → ℝ, P.evaluate x (fun _ => 0) = PolynomialValue a x) ∧
  ∀ η : ℝ, 0 < η → η < 1 →
    ∃ u : ℝ, 0 < u ∧ u < 1 ∧
      ∀ x : Fin a.n → ℝ, ∀ δ : Fin P.roundedCount → ℝ,
        (∀ j, |δ j| ≤ u) →
          |P.evaluate x δ - PolynomialValue a x| ≤ η * |PolynomialValue a x|

def AccuratelyEvaluable (a : PolynomialInput) : Prop :=
  ∃ P : Program a.n, Accurate a P

end NLA.Computation.RoundedTree
