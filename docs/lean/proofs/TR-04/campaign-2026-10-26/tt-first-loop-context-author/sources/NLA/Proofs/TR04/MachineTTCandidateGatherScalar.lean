import NLA.Proofs.TR04.MachineTTFirstSelectionFamily
import NLA.Proofs.TR04.MachineTTHeaderDispatch

/-! Literal candidate-loop entry, gather-bank setup, and return to metadata.
All program syntax is fixed and no future child response is an input. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

private theorem code189 : ttProgram.code 189 = .lessNat 76 75 190 357 := rfl
private theorem code190 : ttProgram.code 190 = .copyNat 27 81 191 := rfl
private theorem code191 : ttProgram.code 191 = .copyNat 28 77 192 := rfl
private theorem code192 : ttProgram.code 192 = .copyNat 29 78 193 := rfl
private theorem code193 : ttProgram.code 193 = .copyNat 30 79 194 := rfl
private theorem code194 : ttProgram.code 194 = .copyNat 31 76 195 := rfl
private theorem code195 : ttProgram.code 195 = .copyNat 32 72 196 := rfl
private theorem code196 : ttProgram.code 196 = .copyNat 33 67 197 := rfl
private theorem code197 : ttProgram.code 197 = .jump 40 := rfl
private theorem code198 : ttProgram.code 198 = .natural 84 0 199 := rfl
private theorem code199 : ttProgram.code 199 = .copyNat 85 81 200 := rfl
private theorem code200 : ttProgram.code 200 = .copyNat 86 106 201 := rfl
private theorem code201 : ttProgram.code 201 = .copyNat 87 82 202 := rfl
private theorem code202 : ttProgram.code 202 = .copyNat 88 106 203 := rfl
private theorem code203 : ttProgram.code 203 = .copyNat 94 67 204 := rfl
private theorem code204 : ttProgram.code 204 = .copyNat 89 92 205 := rfl
private theorem code205 : ttProgram.code 205 = .copyNat 90 69 206 := rfl
private theorem code206 : ttProgram.code 206 = .natural 108 0 207 := rfl
private theorem code207 : ttProgram.code 207 = .jump 241 := rfl

def ttCandidateEntryResult (s : State ttProgram) : State ttProgram :=
  { s with
    label := 40
    natural := Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update s.natural
        27 (s.natural 81)) 28 (s.natural 77)) 29 (s.natural 78)) 30 (s.natural 79))
        31 (s.natural 76)) 32 (s.natural 72)) 33 (s.natural 67) }

def ttCandidateMetadataResult (s : State ttProgram) : State ttProgram :=
  { s with
    label := 241
    natural := Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update s.natural 84 0) 85 (s.natural 81))
          86 (s.natural 106)) 87 (s.natural 82)) 88 (s.natural 106))
          94 (s.natural 67)) 89 (s.natural 92)) 90 (s.natural 69)) 108 0 }

theorem ttCandidate_entry_nine (s : State ttProgram)
    (hl : s.label = 189) (hs : s.status = .running) (hj : s.natural 76 < s.natural 75) :
    (ordinaryStep ttProgram)^[9] s = ttCandidateEntryResult s := by
  classical
  apply machineState_ext
  all_goals simp (disch := decide) only
    [Function.iterate_zero_apply, Function.iterate_succ_apply', ordinaryStep,
      Function.update_apply, if_pos, if_neg, hl, hs, hj, ttCandidateEntryResult,
      code189, code190, code191, code192, code193, code194, code195, code196, code197]

theorem ttCandidate_return_eleven (s : State ttProgram)
    (hl : s.label = 65) (hs : s.status = .running) :
    (ordinaryStep ttProgram)^[11] s = ttCandidateMetadataResult s := by
  classical
  apply machineState_ext
  all_goals simp (disch := decide) only
    [Function.iterate_zero_apply, Function.iterate_succ_apply', ordinaryStep,
      Function.update_apply, if_pos, if_neg, hl, hs, ttProgram_code_gather_exit,
      ttCandidateMetadataResult, code198, code199, code200, code201, code202, code203, code204, code205, code206, code207]

theorem ttCandidate_entry_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label = 189) (hs : (trace.state offset).status = .running)
    (hj : (trace.state offset).natural 76 < (trace.state offset).natural 75) :
    trace.state (offset + 9) = ttCandidateEntryResult (trace.state offset) ∧
      CostThrough ttProgram trace (offset + 9) ≤ CostThrough ttProgram trace offset + 9 := by
  have hx := ttCandidate_entry_nine (trace.state offset) hl hs hj
  have hn : ((ordinaryStep ttProgram)^[9] (trace.state offset)).status = .running := by rw [hx]; exact hs
  obtain ⟨hv, hc⟩ := trace_scalar_block_at ht offset 9
    (fun j hj _ => ttOrdinary_nosvd_prefix_of_running _ _ hn j hj)
  exact ⟨hv.trans hx, hc⟩

theorem ttCandidate_return_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label = 65) (hs : (trace.state offset).status = .running) :
    trace.state (offset + 11) = ttCandidateMetadataResult (trace.state offset) ∧
      CostThrough ttProgram trace (offset + 11) ≤ CostThrough ttProgram trace offset + 11 := by
  have hx := ttCandidate_return_eleven (trace.state offset) hl hs
  have hn : ((ordinaryStep ttProgram)^[11] (trace.state offset)).status = .running := by rw [hx]; exact hs
  obtain ⟨hv, hc⟩ := trace_scalar_block_at ht offset 11
    (fun j hj _ => ttOrdinary_nosvd_prefix_of_running _ _ hn j hj)
  exact ⟨hv.trans hx, hc⟩

#assert_trust kernel ttCandidate_entry_nine
#assert_trust kernel ttCandidate_return_eleven
#assert_trust kernel ttCandidate_entry_at
#assert_trust kernel ttCandidate_return_at
#print axioms ttCandidate_return_at
end NLA.Proofs.TR04
