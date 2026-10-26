import NLA.Proofs.TR04.MachineTTHeaderDispatch
import NLA.Proofs.TR04.MachineHeaderProductRange

/-! Literal mode/suffix/rank call preparation and finite minimum branches before
its first SVD. End-state formulas describe proved instruction execution. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

instance ttInitScalar_nonzero_reals : NeZero ttProgram.realRegisters := ⟨by decide⟩
private theorem ttInitScalar_labels : ttProgram.extraLabels=511 := rfl
private theorem ttInitScalar_naturals : ttProgram.extraNatRegisters=127 := rfl
private theorem ttInitScalar_reals : ttProgram.realRegisters=16 := rfl
private theorem ttInit_code144 : ttProgram.code 144=.copyNat 81 2 145 := rfl
private theorem ttInit_code145 : ttProgram.code 145=.copyNat 1 126 146 := rfl
private theorem ttInit_code146 : ttProgram.code 146=.natural 2 1 147 := rfl
private theorem ttInit_code147 : ttProgram.code 147=.natural 3 0 148 := rfl
private theorem ttInit_code148 : ttProgram.code 148=.natural 97 2 149 := rfl
private theorem ttInit_code149 : ttProgram.code 149=.jump 2 := rfl
private theorem ttInit_code150 : ttProgram.code 150=.copyNat 82 2 151 := rfl
private theorem ttInit_code151 : ttProgram.code 151=.read 0 0 152 := rfl
private theorem ttInit_code152 : ttProgram.code 152=.copyNat 1 0 153 := rfl
private theorem ttInit_code153 : ttProgram.code 153=.natural 2 1 154 := rfl
private theorem ttInit_code154 : ttProgram.code 154=.natural 3 0 155 := rfl
private theorem ttInit_code155 : ttProgram.code 155=.natural 97 3 156 := rfl
private theorem ttInit_code156 : ttProgram.code 156=.jump 5 := rfl
private theorem ttInit_code157 : ttProgram.code 157=.copyNat 80 2 158 := rfl
private theorem ttInit_code158 : ttProgram.code 158=.copyNat 105 81 159 := rfl
private theorem ttInit_code159 : ttProgram.code 159=.lessNat 82 105 160 161 := rfl
private theorem ttInit_code160 : ttProgram.code 160=.copyNat 105 82 161 := rfl
private theorem ttInit_code161 : ttProgram.code 161=.copyNat 86 80 162 := rfl
private theorem ttInit_code162 : ttProgram.code 162=.lessNat 81 86 163 164 := rfl
private theorem ttInit_code163 : ttProgram.code 163=.copyNat 86 81 164 := rfl
private theorem ttInit_code164 : ttProgram.code 164=.lessNat 82 86 165 166 := rfl
private theorem ttInit_code165 : ttProgram.code 165=.copyNat 86 82 166 := rfl
private theorem ttInit_code166 : ttProgram.code 166=.copyNat 106 86 167 := rfl

def ttModeSuffixEntry (s : State ttProgram) : State ttProgram :=
  { s with
    label := 2
    natural := Function.update (Function.update (Function.update (Function.update
      (Function.update s.natural 81 (s.natural 2)) 1 1) 2 1) 3 0) 97 2 }

theorem ttModeSuffix_steps (s : State ttProgram) (hl : s.label=144)
    (hs : s.status=.running) (hone : s.natural 126=1) :
    (ordinaryStep ttProgram)^[6] s=ttModeSuffixEntry s := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.update_apply,Function.update_idem,dite_eq_ite,
    ttInitScalar_labels,ttInitScalar_naturals,ttInitScalar_reals,
    Function.iterate_succ_apply',ordinaryStep,hl,hs,hone,
    ttInit_code144,ttInit_code145,ttInit_code146,ttInit_code147,ttInit_code148,ttInit_code149,
    ttModeSuffixEntry]

def ttColsRankEntry (s : State ttProgram) : State ttProgram :=
  { s with
    label := 5
    real := Function.update s.real 0 (s.memory (s.natural 0))
    natural := Function.update (Function.update (Function.update (Function.update
      (Function.update s.natural 82 (s.natural 2)) 1 (s.natural 0)) 2 1) 3 0) 97 3 }

theorem ttColsRank_steps (s : State ttProgram) (hl : s.label=150)
    (hs : s.status=.running) :
    (ordinaryStep ttProgram)^[7] s=ttColsRankEntry s := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.update_apply,Function.update_idem,dite_eq_ite,
    ttInitScalar_labels,ttInitScalar_naturals,ttInitScalar_reals,
    Function.iterate_succ_apply',ordinaryStep,hl,hs,
    ttInit_code150,ttInit_code151,ttInit_code152,ttInit_code153,ttInit_code154,ttInit_code155,
    ttInit_code156,ttColsRankEntry]

def ttFirstMinRowsEnd (s : State ttProgram) : State ttProgram :=
  { s with
    label := 161
    natural := Function.update (Function.update s.natural 80 (s.natural 2))
      105 (min (s.natural 81) (s.natural 82)) }

theorem ttFirstMinRows_steps (s : State ttProgram) (hl : s.label=157)
    (hs : s.status=.running) :
    ∃ n : ℕ, n≤4 ∧ (ordinaryStep ttProgram)^[n] s=ttFirstMinRowsEnd s := by
  by_cases h : s.natural 82<s.natural 81
  · refine ⟨4,by omega,?_⟩
    have he : min (s.natural 81) (s.natural 82)=s.natural 82 := min_eq_right (by omega)
    apply machineState_ext
    all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,Function.update_apply,Function.update_idem,dite_eq_ite,
      ttInitScalar_labels,ttInitScalar_naturals,ttInitScalar_reals,
      Function.iterate_succ_apply',ordinaryStep,hl,hs,h,he,
      ttInit_code157,ttInit_code158,ttInit_code159,ttInit_code160,ttFirstMinRowsEnd]
  · refine ⟨3,by omega,?_⟩
    have he : min (s.natural 81) (s.natural 82)=s.natural 81 := min_eq_left (by omega)
    apply machineState_ext
    all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,Function.update_apply,Function.update_idem,dite_eq_ite,
      ttInitScalar_labels,ttInitScalar_naturals,ttInitScalar_reals,
      Function.iterate_succ_apply',ordinaryStep,hl,hs,h,he,
      ttInit_code157,ttInit_code158,ttInit_code159,ttInit_code160,ttFirstMinRowsEnd]

def ttFirstMinCapRowsEnd (s : State ttProgram) : State ttProgram :=
  { s with
    label := 164
    natural := Function.update s.natural 86 (min (s.natural 80) (s.natural 81)) }

theorem ttFirstMinCapRows_steps (s : State ttProgram) (hl : s.label=161)
    (hs : s.status=.running) :
    ∃ n : ℕ, n≤3 ∧ (ordinaryStep ttProgram)^[n] s=ttFirstMinCapRowsEnd s := by
  by_cases h : s.natural 81<s.natural 80
  · refine ⟨3,by omega,?_⟩
    have he : min (s.natural 80) (s.natural 81)=s.natural 81 := min_eq_right (by omega)
    apply machineState_ext
    all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,Function.update_apply,Function.update_idem,dite_eq_ite,
      ttInitScalar_labels,ttInitScalar_naturals,ttInitScalar_reals,
      Function.iterate_succ_apply',ordinaryStep,hl,hs,h,he,
      ttInit_code161,ttInit_code162,ttInit_code163,ttFirstMinCapRowsEnd]
  · refine ⟨2,by omega,?_⟩
    have he : min (s.natural 80) (s.natural 81)=s.natural 80 := min_eq_left (by omega)
    apply machineState_ext
    all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,Function.update_apply,Function.update_idem,dite_eq_ite,
      ttInitScalar_labels,ttInitScalar_naturals,ttInitScalar_reals,
      Function.iterate_succ_apply',ordinaryStep,hl,hs,h,he,
      ttInit_code161,ttInit_code162,ttInit_code163,ttFirstMinCapRowsEnd]

def ttFirstMinCapColsEnd (s : State ttProgram) : State ttProgram :=
  { s with
    label := 167
    natural := Function.update (Function.update s.natural
      86 (min (s.natural 86) (s.natural 82))) 106 (min (s.natural 86) (s.natural 82)) }

theorem ttFirstMinCapCols_steps (s : State ttProgram) (hl : s.label=164)
    (hs : s.status=.running) :
    ∃ n : ℕ, n≤3 ∧ (ordinaryStep ttProgram)^[n] s=ttFirstMinCapColsEnd s := by
  by_cases h : s.natural 82<s.natural 86
  · refine ⟨3,by omega,?_⟩
    have he : min (s.natural 86) (s.natural 82)=s.natural 82 := min_eq_right (by omega)
    apply machineState_ext
    all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,Function.update_apply,Function.update_idem,dite_eq_ite,
      ttInitScalar_labels,ttInitScalar_naturals,ttInitScalar_reals,
      Function.iterate_succ_apply',ordinaryStep,hl,hs,h,he,
      ttInit_code164,ttInit_code165,ttInit_code166,ttFirstMinCapColsEnd]
  · refine ⟨2,by omega,?_⟩
    have he : min (s.natural 86) (s.natural 82)=s.natural 86 := min_eq_left (by omega)
    apply machineState_ext
    all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,Function.update_apply,Function.update_idem,dite_eq_ite,
      ttInitScalar_labels,ttInitScalar_naturals,ttInitScalar_reals,
      Function.iterate_succ_apply',ordinaryStep,hl,hs,h,he,
      ttInit_code164,ttInit_code165,ttInit_code166,ttFirstMinCapColsEnd]

def ttFirstRankEnd (s : State ttProgram) : State ttProgram :=
  ttFirstMinCapColsEnd (ttFirstMinCapRowsEnd (ttFirstMinRowsEnd s))

theorem ttFirstRank_steps (s : State ttProgram) (hl : s.label=157)
    (hs : s.status=.running) :
    ∃ n : ℕ, n≤10 ∧ (ordinaryStep ttProgram)^[n] s=ttFirstRankEnd s := by
  obtain ⟨n1,hn1,h1⟩ := ttFirstMinRows_steps s hl hs
  obtain ⟨n2,hn2,h2⟩ := ttFirstMinCapRows_steps (ttFirstMinRowsEnd s) rfl hs
  obtain ⟨n3,hn3,h3⟩ := ttFirstMinCapCols_steps
    (ttFirstMinCapRowsEnd (ttFirstMinRowsEnd s)) rfl hs
  refine ⟨n1+n2+n3,by omega,?_⟩
  rw [Nat.add_comm (n1+n2) n3,Function.iterate_add_apply,
    Nat.add_comm n1 n2,Function.iterate_add_apply,h1,h2,h3]
  rfl

#assert_trust kernel ttModeSuffix_steps
#assert_trust kernel ttColsRank_steps
#assert_trust kernel ttFirstMinRows_steps
#assert_trust kernel ttFirstMinCapRows_steps
#assert_trust kernel ttFirstMinCapCols_steps
#assert_trust kernel ttFirstRank_steps
#print axioms ttFirstRank_steps
end NLA.Proofs.TR04
