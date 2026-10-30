import NLA.Proofs.TR04.MachineTTInitialShape

/-! Literal read-only child-mode/suffix/rank call preparation and finite cap
branches. These are the actual controller instructions before child SVD237. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

private theorem code208 : ttProgram.code 208 = .read 0 84 209 := rfl
private theorem code209 : ttProgram.code 209 = .copyNat 1 0 210 := rfl
private theorem code210 : ttProgram.code 210 = .natural 2 1 211 := rfl
private theorem code211 : ttProgram.code 211 = .natural 3 0 212 := rfl
private theorem code212 : ttProgram.code 212 = .natural 97 4 213 := rfl
private theorem code213 : ttProgram.code 213 = .jump 5 := rfl
private theorem code214 : ttProgram.code 214 = .copyNat 109 2 215 := rfl
private theorem code215 : ttProgram.code 215 = .mulNat 85 100 109 216 := rfl
private theorem code216 : ttProgram.code 216 = .copyNat 1 84 217 := rfl
private theorem code217 : ttProgram.code 217 = .increment 1 218 := rfl
private theorem code218 : ttProgram.code 218 = .natural 2 1 219 := rfl
private theorem code219 : ttProgram.code 219 = .natural 3 0 220 := rfl
private theorem code220 : ttProgram.code 220 = .natural 97 5 221 := rfl
private theorem code221 : ttProgram.code 221 = .jump 2 := rfl
private theorem code222 : ttProgram.code 222 = .copyNat 87 2 223 := rfl
private theorem code223 : ttProgram.code 223 = .addNat 122 0 84 224 := rfl
private theorem code224 : ttProgram.code 224 = .read 0 122 225 := rfl
private theorem code225 : ttProgram.code 225 = .copyNat 1 0 226 := rfl
private theorem code226 : ttProgram.code 226 = .natural 2 1 227 := rfl
private theorem code227 : ttProgram.code 227 = .natural 3 0 228 := rfl
private theorem code228 : ttProgram.code 228 = .natural 97 6 229 := rfl
private theorem code229 : ttProgram.code 229 = .jump 5 := rfl
private theorem code230 : ttProgram.code 230 = .copyNat 86 2 231 := rfl
private theorem code231 : ttProgram.code 231 = .lessNat 85 86 232 233 := rfl
private theorem code232 : ttProgram.code 232 = .copyNat 86 85 233 := rfl
private theorem code233 : ttProgram.code 233 = .lessNat 87 86 234 235 := rfl
private theorem code234 : ttProgram.code 234 = .copyNat 86 87 235 := rfl
private theorem code235 : ttProgram.code 235 = .mulNat 94 84 66 236 := rfl
private theorem code236 : ttProgram.code 236 = .addNat 94 67 94 237 := rfl

def ttChildModeEntry (s : State ttProgram) : State ttProgram :=
  { s with
    label := 5
    real := Function.update s.real 0 (s.memory (s.natural 84))
    natural := Function.update (Function.update (Function.update (Function.update s.natural
      1 (s.natural 0)) 2 1) 3 0) 97 4 }

def ttChildSuffixEntry (s : State ttProgram) : State ttProgram :=
  { s with
    label := 2
    natural := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update s.natural 109 (s.natural 2)) 85 (s.natural 100 * s.natural 2))
        1 (s.natural 84 + 1)) 2 1) 3 0) 97 5 }

def ttChildRankEntry (s : State ttProgram) : State ttProgram :=
  { s with
    label := 5
    real := Function.update s.real 0 (s.memory (s.natural 0 + s.natural 84))
    natural := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update s.natural 87 (s.natural 2)) 122 (s.natural 0 + s.natural 84))
        1 (s.natural 0)) 2 1) 3 0) 97 6 }

def ttChildCapRowsEnd (s : State ttProgram) : State ttProgram :=
  { s with label := 233, natural := Function.update s.natural 86 (min (s.natural 2) (s.natural 85)) }

def ttChildCapColsEnd (s : State ttProgram) : State ttProgram :=
  { s with
    label := 237
    natural := Function.update (Function.update s.natural 86 (min (s.natural 86) (s.natural 87)))
      94 (s.natural 67 + s.natural 84 * s.natural 66) }

def ttChildCapEnd (s : State ttProgram) : State ttProgram := ttChildCapColsEnd (ttChildCapRowsEnd s)

theorem ttChild_mode_steps (s : State ttProgram) (hl : s.label = 208) (hs : s.status = .running) :
    (ordinaryStep ttProgram)^[6] s = ttChildModeEntry s := by
  classical
  apply machineState_ext
  all_goals simp (disch := decide) only [Function.iterate_zero_apply, Function.iterate_succ_apply',
    ordinaryStep, Function.update_apply, Function.update_idem, Function.update_eq_self, if_pos, if_neg, hl, hs, ttChildModeEntry, code208, code209, code210, code211, code212, code213]

theorem ttChild_suffix_steps (s : State ttProgram) (hl : s.label = 214) (hs : s.status = .running) :
    (ordinaryStep ttProgram)^[8] s = ttChildSuffixEntry s := by
  classical
  apply machineState_ext
  all_goals simp (disch := decide) only [Function.iterate_zero_apply, Function.iterate_succ_apply',
    ordinaryStep, Function.update_apply, Function.update_idem, Function.update_eq_self, if_pos, if_neg, hl, hs, ttChildSuffixEntry, code214, code215, code216, code217, code218, code219, code220, code221]

theorem ttChild_rank_steps (s : State ttProgram) (hl : s.label = 222) (hs : s.status = .running) :
    (ordinaryStep ttProgram)^[8] s = ttChildRankEntry s := by
  classical
  apply machineState_ext
  all_goals simp (disch := decide) only [Function.iterate_zero_apply, Function.iterate_succ_apply',
    ordinaryStep, Function.update_apply, Function.update_idem, Function.update_eq_self, if_pos, if_neg, hl, hs, ttChildRankEntry, code222, code223, code224, code225, code226, code227, code228, code229]

theorem ttChild_cap_rows_steps (s : State ttProgram) (hl : s.label = 230) (hs : s.status = .running) :
    ∃ n : ℕ, n ≤ 3 ∧ (ordinaryStep ttProgram)^[n] s = ttChildCapRowsEnd s := by
  classical
  by_cases h : s.natural 85 < s.natural 2
  · refine ⟨3, by omega, ?_⟩
    have he : min (s.natural 2) (s.natural 85) = s.natural 85 := min_eq_right (by omega)
    apply machineState_ext
    all_goals simp (disch := decide) only [Function.iterate_zero_apply, Function.iterate_succ_apply',
      ordinaryStep, Function.update_apply, Function.update_idem, Function.update_eq_self, if_pos, if_neg,
      hl, hs, h, he, ttChildCapRowsEnd, code230, code231, code232]
  · refine ⟨2, by omega, ?_⟩
    have he : min (s.natural 2) (s.natural 85) = s.natural 2 := min_eq_left (by omega)
    apply machineState_ext
    all_goals simp (disch := decide) only [Function.iterate_zero_apply, Function.iterate_succ_apply',
      ordinaryStep, Function.update_apply, Function.update_idem, Function.update_eq_self, if_pos, if_neg,
      hl, hs, h, he, ttChildCapRowsEnd, code230, code231]

theorem ttChild_cap_cols_steps (s : State ttProgram) (hl : s.label = 233) (hs : s.status = .running) :
    ∃ n : ℕ, n ≤ 4 ∧ (ordinaryStep ttProgram)^[n] s = ttChildCapColsEnd s := by
  classical
  by_cases h : s.natural 87 < s.natural 86
  · refine ⟨4, by omega, ?_⟩
    have he : min (s.natural 86) (s.natural 87) = s.natural 87 := min_eq_right (by omega)
    apply machineState_ext
    all_goals simp (disch := decide) only [Function.iterate_zero_apply, Function.iterate_succ_apply',
      ordinaryStep, Function.update_apply, Function.update_idem, Function.update_eq_self, if_pos, if_neg,
      hl, hs, h, he, ttChildCapColsEnd, code233, code234, code235, code236]
  · refine ⟨3, by omega, ?_⟩
    have he : min (s.natural 86) (s.natural 87) = s.natural 86 := min_eq_left (by omega)
    apply machineState_ext
    all_goals simp (disch := decide) only [Function.iterate_zero_apply, Function.iterate_succ_apply',
      ordinaryStep, Function.update_apply, Function.update_idem, Function.update_eq_self, if_pos, if_neg,
      hl, hs, h, he, ttChildCapColsEnd, code233, code235, code236]

theorem ttChild_cap_steps (s : State ttProgram) (hl : s.label = 230) (hs : s.status = .running) :
    ∃ n : ℕ, n ≤ 7 ∧ (ordinaryStep ttProgram)^[n] s = ttChildCapEnd s := by
  obtain ⟨n1, hn1, h1⟩ := ttChild_cap_rows_steps s hl hs
  obtain ⟨n2, hn2, h2⟩ := ttChild_cap_cols_steps (ttChildCapRowsEnd s) rfl hs
  refine ⟨n1 + n2, by omega, ?_⟩
  rw [Nat.add_comm n1 n2, Function.iterate_add_apply, h1, h2]
  rfl

#assert_trust kernel ttChild_mode_steps
#assert_trust kernel ttChild_suffix_steps
#assert_trust kernel ttChild_rank_steps
#assert_trust kernel ttChild_cap_rows_steps
#assert_trust kernel ttChild_cap_cols_steps
#assert_trust kernel ttChild_cap_steps
#print axioms ttChild_cap_steps
end NLA.Proofs.TR04
