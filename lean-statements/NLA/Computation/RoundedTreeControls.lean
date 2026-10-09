import NLA.Computation.RoundedTree
import Mathlib.Tactic.NormNum
import LeanCert.Tactic.Verification

/-! Small symbolic kernel controls for stored arithmetic, exact comparisons,
all-branch error numbering and the zero-variable convention. These prove no
catalog decision theorem and use no native computation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Computation.RoundedTreeControls

open RoundedTree BinaryEncoding

/-- The one rounded sum is read twice by the product. -/
def storedSquare : Program 1 :=
  .rounded .add 0 0 (.rounded .multiply 1 1 (.ret 2))

theorem stored_count : storedSquare.roundedCount = 2 := rfl

theorem stored_error_reused (x : ℝ) (δ : Fin 2 → ℝ) :
    storedSquare.evaluate (fun _ => x) δ =
      ((x + x) * (1 + δ 0)) ^ 2 * (1 + δ 1) := by
  simp [storedSquare, Program.evaluate, Program.roundedCount, BinaryOp.apply,
    Fin.snoc, pow_two]

/-- Equal operands at two separate rounded nodes still use distinct errors. -/
def recomputeDifference : Program 1 :=
  .rounded .add 0 0 (.rounded .add 0 0 (.rounded .subtract 1 2 (.ret 3)))

theorem recomputation_errors_separate (x : ℝ) (δ : Fin 3 → ℝ) :
    recomputeDifference.evaluate (fun _ => x) δ =
      ((x + x) * (1 + δ 0) - (x + x) * (1 + δ 1)) * (1 + δ 2) := by
  simp [recomputeDifference, Program.evaluate, Program.roundedCount, BinaryOp.apply, Fin.snoc]

def negateInput : Program 1 := .negate 0 (.ret 1)

theorem negation_is_exact (x : ℝ) (δ : Fin 0 → ℝ) :
    negateInput.evaluate (fun _ => x) δ = -x := by
  simp [negateInput, Program.evaluate, Fin.snoc]

/-- The same comparison tests actual rounded registers, including equality. -/
def errorDependentBranch : Program 1 :=
  .rounded .add 0 0 (.rounded .add 0 0 (.compare 1 2 (.ret 1) (.ret 0) (.ret 2)))

theorem equality_branch_at_zero_error :
    errorDependentBranch.evaluate (fun _ => 1) ![0, 0] = 1 := by
  simp only [errorDependentBranch, Program.evaluate]
  norm_num [Program.roundedCount, BinaryOp.apply, Fin.snoc, errorSlice,
    Matrix.cons_val_zero', Matrix.cons_val_succ]
  change (if (0 : ℝ) < 0 then 2 * (1 + 0)
    else if (0 : ℝ) = 0 then 1 else 2 * (1 + 0)) = 1
  norm_num

theorem different_branch_with_rounding :
    errorDependentBranch.evaluate (fun _ => 1) ![0, (1 / 4 : ℝ)] = 2 := by
  simp only [errorDependentBranch, Program.evaluate]
  norm_num [Program.roundedCount, BinaryOp.apply, Fin.snoc, errorSlice,
    Matrix.cons_val_zero', Matrix.cons_val_succ]
  change (if (0 : ℝ) < 1 / 4 then 2 * (1 + 0)
    else if (0 : ℝ) = 1 / 4 then 1 else 2 * (1 + 1 / 4)) = 2
  norm_num

/-- The less/equal/greater subtrees contain one, two and one rounded nodes. -/
def unequalBranchSizes : Program 2 :=
  .compare 0 1
    (.rounded .add 0 1 (.ret 2))
    (.rounded .subtract 0 1 (.rounded .add 2 0 (.ret 3)))
    (.rounded .multiply 0 1 (.ret 2))

theorem all_branches_counted : unequalBranchSizes.roundedCount = 4 := rfl

theorem greater_uses_static_fourth_error (δ : Fin 4 → ℝ) :
    unequalBranchSizes.evaluate ![3, 1] δ = 3 * (1 + δ 3) := by
  simp only [unequalBranchSizes, Program.evaluate]
  norm_num [Program.roundedCount, BinaryOp.apply, Fin.snoc, errorSlice]
  rfl

theorem equal_uses_static_middle_block (δ : Fin 4 → ℝ) :
    unequalBranchSizes.evaluate ![2, 2] δ = 2 * (1 + δ 2) := by
  simp only [unequalBranchSizes, Program.evaluate]
  norm_num [Program.roundedCount, BinaryOp.apply, Fin.snoc, errorSlice]
  rfl

theorem unused_branches_ignored (δ ε : Fin 4 → ℝ) (h : δ 3 = ε 3) :
    unequalBranchSizes.evaluate ![3, 1] δ = unequalBranchSizes.evaluate ![3, 1] ε := by
  rw [greater_uses_static_fourth_error, greater_uses_static_fourth_error, h]

/-- Full explicit coefficient/exponent syntax, with no numerical evaluator literals. -/
def samplePolynomial : PolynomialInput :=
  ⟨2, [⟨-3, ![2, 0]⟩, ⟨5, ![0, 1]⟩]⟩

theorem integer_list_grammar :
    encodePolynomial samplePolynomial =
      encodeNat 2 ++ encodeNat 2 ++ encodeInt (-3) ++ encodeNat 2 ++ encodeNat 0 ++
        encodeInt 5 ++ encodeNat 0 ++ encodeNat 1 := by
  simp [encodePolynomial, encodeTerm, samplePolynomial, List.ofFn_succ, List.append_assoc]

private abbrev zeroPolynomial (n : ℕ) : PolynomialInput := ⟨n, []⟩

def zeroFromInput : Program 1 := .rounded .subtract 0 0 (.ret 1)

/-- Uniform exact output at a polynomial zero survives every error value. -/
theorem zero_tree_accurate : Accurate (zeroPolynomial 1) zeroFromInput := by
  constructor
  · intro x
    simp [zeroFromInput, Program.evaluate, Program.roundedCount, BinaryOp.apply,
      Fin.snoc, PolynomialValue]
  · intro η _ _
    refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    intro x δ _
    simp [zeroFromInput, Program.evaluate, Program.roundedCount, BinaryOp.apply,
      Fin.snoc, PolynomialValue]

/-- The degenerate zero-variable zero polynomial is valid but has no tree. -/
theorem zero_variable_convention : ValidInput (zeroPolynomial 0) ∧
    ¬ AccuratelyEvaluable (zeroPolynomial 0) := by
  constructor
  · simp [ValidInput, PolynomialValue]
  · rintro ⟨P, _⟩
    exact no_program_zero P

/-- Constant cancellation is tested after summing all coefficient occurrences. -/
private abbrev cancellingConstants : PolynomialInput :=
  ⟨0, [⟨3, Fin.elim0⟩, ⟨-3, Fin.elim0⟩]⟩

theorem collected_constant_guard : ValidInput cancellingConstants := by
  norm_num [ValidInput, PolynomialValue]

#assert_trust kernel stored_error_reused
#assert_trust kernel recomputation_errors_separate
#assert_trust kernel negation_is_exact
#assert_trust kernel equality_branch_at_zero_error
#assert_trust kernel different_branch_with_rounding
#assert_trust kernel greater_uses_static_fourth_error
#assert_trust kernel equal_uses_static_middle_block
#assert_trust kernel unused_branches_ignored
#assert_trust kernel integer_list_grammar
#assert_trust kernel zero_tree_accurate
#assert_trust kernel zero_variable_convention
#assert_trust kernel collected_constant_guard

end NLA.Computation.RoundedTreeControls
