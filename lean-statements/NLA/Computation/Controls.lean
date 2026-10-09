import NLA.Computation.FiniteMachine
import NLA.Computation.BinaryEncoding
import LeanCert.Tactic.Verification

/-! Kernel-checked semantic regression examples for the shared model.
These test syntax and actual machine execution, not any catalog target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Computation.Controls

open BinaryEncoding

theorem natural_encoding_length (n : ℕ) :
    (encodeNat n).length = 2 * (binary n).length + 1 := by
  simp [encodeNat]
  omega

theorem framed_length_recovers (n : ℕ) (tail : BinaryEncoding.Word) :
    parseLength (List.replicate n true ++ false :: tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, parseLength, ih]

theorem encode_zero : encodeNat 0 = [true, false, false] := by decide
theorem encode_five : encodeNat 5 =
    [true, true, true, false, true, false, true] := by decide
theorem parse_zero_suffix : parseNat (encodeNat 0 ++ [true, false]) =
    some (0, [true, false]) := by decide
theorem parse_large_numeral : parseNat (encodeNat 257) = some (257, []) := by decide
theorem reject_empty_numeral : parseNat [false] = none := by decide
theorem reject_missing_separator : parseNat [true, true] = none := by decide
theorem reject_truncated_numeral : parseNat [true, true, false, true] = none := by decide
theorem reject_leading_zero : parseNat [true, true, false, false, true] = none := by decide
theorem reject_negative_zero : parseInt (true :: encodeNat 0) = none := by decide
theorem parse_negative : parseInt (encodeInt (-17)) = some (-17, []) := by decide
theorem parse_fraction : parseRat (encodeRat (mkRat (-3) 5)) =
    some (mkRat (-3) 5, []) := by decide
theorem parse_rational_zero : parseRat (encodeRat 0) = some (0, []) := by decide
theorem reject_zero_denominator : parseRat (encodeInt 1 ++ encodeNat 0) = none := by decide
theorem reject_unreduced : parseRat (encodeInt 2 ++ encodeNat 2) = none := by decide
theorem reject_noncanonical_zero : parseRat (encodeInt 0 ++ encodeNat 2) = none := by decide
theorem reject_short_field_list : (parseRats 100 [true, false]).isNone = true := by decide

def avExample : AVInput :=
  ⟨2, fun i j => if i = j then (i.val + 1 : ℕ) else -1,
    fun i => if i.val = 0 then mkRat (-3) 5 else 0⟩

theorem matrix_row_major : matrixEntries avExample.matrix = [1, -1, -1, 2] := by decide

theorem av_roundtrip_example :
    (decodeAV (encodeAV avExample)).map
      (fun a => (a.n, matrixEntries a.matrix, vectorEntries a.rhs)) =
    some (2, [1, -1, -1, 2], [mkRat (-3) 5, 0]) := by decide

theorem reject_extra_input : (decodeAV (encodeAV avExample ++ [false])).isNone = true := by decide
theorem reject_missing_matrix : (decodeAV (encodeNat 100)).isNone = true := by decide

theorem threshold_parser_does_not_decide_promise :
    (decodeThreshold (encodeThreshold ⟨1, fun _ _ => 0, -1⟩)).map
      ThresholdInput.threshold = some (-1) := by decide

def intervalExample : IntervalInput :=
  ⟨1, fun _ _ => -2, fun _ _ => 3, fun _ => -4, fun _ => 5⟩

theorem interval_field_order :
    (decodeInterval (encodeInterval intervalExample)).map
      (fun a => (matrixEntries a.lowerMatrix, matrixEntries a.upperMatrix,
        vectorEntries a.lowerRhs, vectorEntries a.upperRhs)) =
    some ([-2], [3], [-4], [5]) := by decide

def outputExample : IntervalOutput := ⟨1, fun _ => mkRat (-1) 3, fun _ => mkRat 2 3⟩

theorem output_field_order :
    (decodeIntervalOutput (encodeIntervalOutput outputExample)).map
      (fun a => (a.n, vectorEntries a.lower, vectorEntries a.upper)) =
    some (1, [mkRat (-1) 3], [mkRat 2 3]) := by decide

theorem output_extra_bit_rejected :
    (decodeIntervalOutput (encodeIntervalOutput outputExample ++ [true])).isNone = true := by decide

/-- A machine that immediately halts; it has one state and no input oracle. -/
def haltMachine : FiniteMachine := ⟨0, fun _ _ => none⟩

/-- A machine that always moves right and never halts, even on a blank tape. -/
def movingMachine : FiniteMachine :=
  ⟨0, fun _ _ => some (0, Turing.TM0.Stmt.move Turing.Dir.right)⟩

theorem halt_preserves_input (w : NLA.Computation.Word) :
    haltMachine.RunsWithin w w 0 := by
  refine ⟨haltMachine.initial w,
    ⟨StateTransition.EvalsToInTime.refl _ _⟩, rfl, ?_⟩
  exact Turing.Tape.mk'_right₀ _ _

theorem output_trailing_zero_is_not_blank :
    ¬ haltMachine.HasOutput (haltMachine.initial [true, false]) [true] := by
  intro h
  have bad := congrArg (fun L : Turing.ListBlank NLA.Computation.Symbol => L.nth 1) h
  change (some false : Option Bool) = none at bad
  contradiction

theorem moving_initial_not_terminal (w : NLA.Computation.Word) :
    movingMachine.step (movingMachine.initial w) ≠ none := by
  simp [FiniteMachine.step, movingMachine, Turing.TM0.step]

theorem reached_is_not_halted (w : NLA.Computation.Word) :
    Nonempty (StateTransition.EvalsToInTime movingMachine.step
      (movingMachine.initial w) (some (movingMachine.initial w)) 0) ∧
    movingMachine.step (movingMachine.initial w) ≠ none :=
  ⟨⟨StateTransition.EvalsToInTime.refl _ _⟩, moving_initial_not_terminal w⟩

#assert_trust kernel encode_zero
#assert_trust kernel natural_encoding_length
#assert_trust kernel framed_length_recovers
#assert_trust kernel parseRats_length
#assert_trust kernel parse_large_numeral
#assert_trust kernel reject_unreduced
#assert_trust kernel av_roundtrip_example
#assert_trust kernel output_field_order
#assert_trust kernel halt_preserves_input
#assert_trust kernel output_trailing_zero_is_not_blank
#assert_trust kernel reached_is_not_halted
#print axioms halt_preserves_input
#print axioms av_roundtrip_example
#print axioms FiniteMachine.RunsWithin

end NLA.Computation.Controls
