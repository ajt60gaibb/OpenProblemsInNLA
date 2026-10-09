import NLA.Computation.OracleMachine
import LeanCert.Tactic.Verification

/-! Kernel checks of query contents, charged steps, oracle branching and
failure semantics. No NP-completeness or catalog target is proved here. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Computation.OracleControls

def answerMachine : OracleMachine :=
  ⟨3, fun state _ _ _ =>
    if state.val = 0 then .work 1 (some (.write (some true))) none (some (.write (some false)))
    else if state.val = 1 then .query 2 3
    else if state.val = 2 then .halt
    else .work 2 (some (.write (some false))) none none⟩

theorem query_is_written_before_call (oracle : Word → Bool) :
    answerMachine.queryWord (answerMachine.run oracle [] 0) = none ∧
    answerMachine.queryWord (answerMachine.run oracle [] 1) = some [false] := by
  constructor <;> rfl

theorem yes_halts_in_three_steps :
    (answerMachine.run (fun _ => true) [] 3).status = .halted := rfl

theorem no_requires_four_steps :
    (answerMachine.run (fun _ => false) [] 3).status = .running ∧
    (answerMachine.run (fun _ => false) [] 4).status = .halted := by
  constructor <;> rfl

theorem yes_output :
    answerMachine.HasOutput (answerMachine.run (fun _ => true) [] 3) [true] := rfl

theorem no_output :
    answerMachine.HasOutput (answerMachine.run (fun _ => false) [] 4) [false] := rfl

theorem exact_query_trace :
    (answerMachine.queryTrace (fun _ => true) [] 3).map
      (fun event => (event.time, event.word)) = [(1, [false])] := rfl

theorem successful_run_with_legal_query :
    answerMachine.RunsWithin (fun _ => true) {[false]} [] [true] 3 := by
  refine ⟨3, by decide, rfl, rfl, ?_⟩
  change ∀ event ∈ [OracleMachine.QueryEvent.mk 1
    (answerMachine.run (fun _ => true) [] 1) [false]], event.word ∈ ({[false]} : Set Word)
  simp

theorem recorded_query_is_not_legal_for_empty_promise :
    ¬ (∀ event ∈ answerMachine.queryTrace (fun _ => true) [] 3,
      event.word ∈ (∅ : Set Word)) := by
  change ¬ (∀ event ∈ [OracleMachine.QueryEvent.mk 1
    (answerMachine.run (fun _ => true) [] 1) [false]], event.word ∈ (∅ : Set Word))
  simp

theorem query_preserves_tapes (oracle : Word → Bool) :
    let before := answerMachine.run oracle [] 1
    let after := answerMachine.step oracle before
    after.main = before.main ∧ after.work = before.work ∧ after.query = before.query := by
  dsimp [OracleMachine.run, OracleMachine.initial, OracleMachine.step, answerMachine,
    QueryTape.read, QueryTape.readSuffix, QueryTape.decodeSymbols, OracleMachine.applyAction]
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- An actual malformed query tape: bit, blank, bit. The main tape already
contains true, so confusing failure with successful halt would be unsound. -/
def malformedMachine : OracleMachine :=
  ⟨0, fun _ _ _ _ => .query 0 0⟩

def malformedConfiguration : malformedMachine.Configuration :=
  ⟨0, Turing.Tape.mk₁ [some true], Turing.Tape.mk₁ [],
    Turing.Tape.mk₁ [some true, none, some false], .running⟩

theorem malformed_query_fails (oracle : Word → Bool) :
    (malformedMachine.step oracle malformedConfiguration).status = .failed := rfl

theorem failure_even_with_output_bit (oracle : Word → Bool) :
    malformedMachine.HasOutput (malformedMachine.step oracle malformedConfiguration) [true] ∧
    (malformedMachine.step oracle malformedConfiguration).status ≠ .halted := by
  exact ⟨rfl, by change (OracleStatus.failed ≠ OracleStatus.halted); decide⟩

theorem malformed_query_never_calls_oracle :
    malformedMachine.queryWord malformedConfiguration = none := rfl

theorem failed_state_absorbs (M : OracleMachine) (oracle : Word → Bool)
    (c : M.Configuration) (h : c.status = .failed) : M.step oracle c = c := by
  simp [OracleMachine.step, h]

theorem halted_state_absorbs (M : OracleMachine) (oracle : Word → Bool)
    (c : M.Configuration) (h : c.status = .halted) : M.step oracle c = c := by
  simp [OracleMachine.step, h]

#assert_trust kernel QueryTape.decodeSymbols_append_blanks
#assert_trust kernel QueryTape.read_input
#assert_trust kernel query_is_written_before_call
#assert_trust kernel yes_halts_in_three_steps
#assert_trust kernel no_requires_four_steps
#assert_trust kernel exact_query_trace
#assert_trust kernel successful_run_with_legal_query
#assert_trust kernel recorded_query_is_not_legal_for_empty_promise
#assert_trust kernel malformed_query_fails
#assert_trust kernel failure_even_with_output_bit
#assert_trust kernel malformed_query_never_calls_oracle
#assert_trust kernel failed_state_absorbs
#print axioms Complexity.InNP
#print axioms Complexity.OracleNPHard

end NLA.Computation.OracleControls
