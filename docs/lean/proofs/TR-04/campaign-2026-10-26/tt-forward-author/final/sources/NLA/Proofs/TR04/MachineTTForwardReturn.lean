import NLA.Proofs.TR04.MachineTTForwardScalar

/-! Actual matrix-return dispatch, first output-buffer selection, child swap,
and forward level update. The reverse branch stops before its decrement. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def ttForwardFirstPointerState (s : State ttProgram) : State ttProgram :=
  { s with
    label := 281
    natural := Function.update (Function.update s.natural (89 : Fin 128) (s.natural (69 : Fin 128))) (90 : Fin 128) (s.natural (70 : Fin 128))
    status := .running }

def ttForwardChildPointerState (s : State ttProgram) : State ttProgram :=
  { s with
    label := 281
    natural := Function.update (Function.update (Function.update s.natural (123 : Fin 128) (s.natural (89 : Fin 128)))
      89 (s.natural (90 : Fin 128))) (90 : Fin 128) (s.natural (89 : Fin 128))
    status := .running }

def ttForwardLevelEnd (s : State ttProgram) : State ttProgram where
  label := if s.natural (84 : Fin 128) + 1 < s.natural (0 : Fin 128) - 1 then 208 else 286
  real := s.real
  natural := Function.update (Function.update (Function.update s.natural (100 : Fin 128) (s.natural (86 : Fin 128)))
    84 (s.natural (84 : Fin 128) + 1)) (110 : Fin 128) (s.natural (0 : Fin 128) - 1)
  memory := s.memory
  status := .running

def ttForwardFirstEnd (s : State ttProgram) : State ttProgram :=
  ttForwardLevelEnd (ttForwardFirstPointerState s)

def ttForwardChildEnd (s : State ttProgram) : State ttProgram :=
  ttForwardLevelEnd (ttForwardChildPointerState s)

 theorem ttForwardFirst_pointer_steps (s : State ttProgram) (hl : s.label=32)
    (hs : s.status=.running) (htag : s.natural 97=0) (hz : s.natural 127=0) :
    (ordinaryStep ttProgram)^[4] s=ttForwardFirstPointerState s := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.iterate_succ_apply',ordinaryStep,hl,hs,htag,hz,
    ttProgram_code_matrix_exit,ttProgram_code_forward_274,ttProgram_code_forward_275,
    ttProgram_code_forward_276,ttForwardFirstPointerState]

 theorem ttForwardChild_pointer_steps (s : State ttProgram) (hl : s.label=32)
    (hs : s.status=.running) (htag : s.natural 97=1)
    (hz : s.natural 127=0) (ho : s.natural 126=1) :
    (ordinaryStep ttProgram)^[6] s=ttForwardChildPointerState s := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.iterate_succ_apply',ordinaryStep,hl,hs,htag,hz,ho,
    ttProgram_code_matrix_exit,ttProgram_code_forward_394,ttProgram_code_forward_277,
    ttProgram_code_forward_278,ttProgram_code_forward_279,ttProgram_code_forward_280,
    ttForwardChildPointerState]

 theorem ttForwardLevel_steps (s : State ttProgram) (hl : s.label=281) (hs : s.status=.running) :
    (ordinaryStep ttProgram)^[5] s=ttForwardLevelEnd s := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.iterate_succ_apply',ordinaryStep,hl,hs,
    ttProgram_code_forward_281,ttProgram_code_forward_282,ttProgram_code_forward_283,
    ttProgram_code_forward_284,ttProgram_code_forward_285,ttForwardLevelEnd,Function.update_idem]

 theorem ttForwardFirst_return_steps (s : State ttProgram) (hl : s.label=32)
    (hs : s.status=.running) (htag : s.natural 97=0) (hz : s.natural 127=0) :
    (ordinaryStep ttProgram)^[9] s=ttForwardFirstEnd s := by
  rw [show 9=5+4 by omega,Function.iterate_add_apply,ttForwardFirst_pointer_steps s hl hs htag hz]
  exact ttForwardLevel_steps _ rfl rfl

 theorem ttForwardChild_return_steps (s : State ttProgram) (hl : s.label=32)
    (hs : s.status=.running) (htag : s.natural 97=1)
    (hz : s.natural 127=0) (ho : s.natural 126=1) :
    (ordinaryStep ttProgram)^[11] s=ttForwardChildEnd s := by
  rw [show 11=5+6 by omega,Function.iterate_add_apply,ttForwardChild_pointer_steps s hl hs htag hz ho]
  exact ttForwardLevel_steps _ rfl rfl

 theorem ttForwardFirst_return_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label=32) (hs : (trace.state offset).status=.running)
    (htag : (trace.state offset).natural 97=0) (hz : (trace.state offset).natural 127=0) :
    trace.state (offset+9)=ttForwardFirstEnd (trace.state offset) ∧
    CostThrough ttProgram trace (offset+9)≤CostThrough ttProgram trace offset+9 := by
  have he := ttForwardFirst_return_steps (trace.state offset) hl hs htag hz
  have hn : ((ordinaryStep ttProgram)^[9] (trace.state offset)).status=.running := by rw [he];rfl
  obtain ⟨hv,hc⟩ := trace_scalar_block_at ht offset 9
    (fun j hj _ => ttOrdinary_nosvd_prefix_of_running _ _ hn j hj)
  exact ⟨hv.trans he,hc⟩

 theorem ttForwardChild_return_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label=32) (hs : (trace.state offset).status=.running)
    (htag : (trace.state offset).natural 97=1) (hz : (trace.state offset).natural 127=0)
    (ho : (trace.state offset).natural 126=1) :
    trace.state (offset+11)=ttForwardChildEnd (trace.state offset) ∧
    CostThrough ttProgram trace (offset+11)≤CostThrough ttProgram trace offset+11 := by
  have he := ttForwardChild_return_steps (trace.state offset) hl hs htag hz ho
  have hn : ((ordinaryStep ttProgram)^[11] (trace.state offset)).status=.running := by rw [he];rfl
  obtain ⟨hv,hc⟩ := trace_scalar_block_at ht offset 11
    (fun j hj _ => ttOrdinary_nosvd_prefix_of_running _ _ hn j hj)
  exact ⟨hv.trans he,hc⟩

def TTForwardReturnStable (i : Fin 128) : Prop :=
  i ≠ 89 ∧ i ≠ 90 ∧ i ≠ 100 ∧ i ≠ 84 ∧ i ≠ 110 ∧ i ≠ 123

 theorem ttForwardFirstEnd_fields (s : State ttProgram) :
    (ttForwardFirstEnd s).label=(if s.natural 84+1<s.natural 0-1 then 208 else 286) ∧
    (ttForwardFirstEnd s).natural 89=s.natural 69 ∧
    (ttForwardFirstEnd s).natural 90=s.natural 70 ∧
    (ttForwardFirstEnd s).natural 100=s.natural 86 ∧
    (ttForwardFirstEnd s).natural 84=s.natural 84+1 ∧
    (ttForwardFirstEnd s).natural 110=s.natural 0-1 ∧
    (ttForwardFirstEnd s).memory=s.memory ∧ (ttForwardFirstEnd s).real=s.real := by
  simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,-Fin.val_eq_zero_iff,
    Fin.ext_iff,show ttProgram.extraNatRegisters+1=128 from rfl,ttForwardFirstEnd,ttForwardLevelEnd,ttForwardFirstPointerState]

 theorem ttForwardChildEnd_fields (s : State ttProgram) :
    (ttForwardChildEnd s).label=(if s.natural 84+1<s.natural 0-1 then 208 else 286) ∧
    (ttForwardChildEnd s).natural 89=s.natural 90 ∧
    (ttForwardChildEnd s).natural 90=s.natural 89 ∧
    (ttForwardChildEnd s).natural 100=s.natural 86 ∧
    (ttForwardChildEnd s).natural 84=s.natural 84+1 ∧
    (ttForwardChildEnd s).natural 110=s.natural 0-1 ∧
    (ttForwardChildEnd s).memory=s.memory ∧ (ttForwardChildEnd s).real=s.real := by
  simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,-Fin.val_eq_zero_iff,
    Fin.ext_iff,show ttProgram.extraNatRegisters+1=128 from rfl,ttForwardChildEnd,ttForwardLevelEnd,ttForwardChildPointerState]

 theorem ttForwardFirstEnd_natural (s : State ttProgram) (i : Fin 128) (hi : TTForwardReturnStable i) :
    (ttForwardFirstEnd s).natural i=s.natural i := by
  rcases hi with ⟨h89,h90,h100,h84,h110,h123⟩
  simp only [ttForwardFirstEnd,ttForwardLevelEnd,ttForwardFirstPointerState,
    Function.update_of_ne h89,Function.update_of_ne h90,Function.update_of_ne h100,
    Function.update_of_ne h84,Function.update_of_ne h110]

 theorem ttForwardChildEnd_natural (s : State ttProgram) (i : Fin 128) (hi : TTForwardReturnStable i) :
    (ttForwardChildEnd s).natural i=s.natural i := by
  rcases hi with ⟨h89,h90,h100,h84,h110,h123⟩
  simp only [ttForwardChildEnd,ttForwardLevelEnd,ttForwardChildPointerState,
    Function.update_of_ne h89,Function.update_of_ne h90,Function.update_of_ne h100,
    Function.update_of_ne h84,Function.update_of_ne h110,Function.update_of_ne h123]

#assert_trust kernel ttForwardFirst_return_steps
#assert_trust kernel ttForwardChild_return_steps
#assert_trust kernel ttForwardFirst_return_at
#assert_trust kernel ttForwardChild_return_at
#print axioms ttForwardFirst_return_at
#print axioms ttForwardChild_return_at
end NLA.Proofs.TR04
