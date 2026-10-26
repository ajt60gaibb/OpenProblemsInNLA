import NLA.Proofs.TR04.MachineTTReverseScalar

/-! Literal reverse lift preparation and return. The stored stride is read from
real metadata by the preceding decoder; this block uses its actual natural
result and the actual level/frame allocation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
private theorem ttReverseLift_labels : ttProgram.extraLabels=511 := rfl
private theorem ttReverseLift_naturals : ttProgram.extraNatRegisters=127 := rfl

def ttReverseLiftDataState (s : State ttProgram) : State ttProgram :=
  { s with
    label := 322
    natural := Function.update (Function.update s.natural (88 : Fin 128) (s.natural 2))
      (94 : Fin 128) (s.natural 67+s.natural 84*s.natural 66)
    status := .running }

 theorem ttReverseLift_data_steps (s : State ttProgram) (hl : s.label=319) (hs : s.status=.running) :
    (ordinaryStep ttProgram)^[3] s=ttReverseLiftDataState s := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,ttReverseLift_labels,Function.iterate_succ_apply',ordinaryStep,hl,hs,
    ttProgram_code_reverse_319,ttProgram_code_reverse_320,ttProgram_code_reverse_321,
    ttReverseLiftDataState,Function.update_idem,ttReverseLift_naturals]

def ttReverseLiftSetupCells (old : Fin 128 → ℕ) : List (Fin 128 × ℕ) :=
  [(4,old 127),(5,old 87),(6,old 127),(7,old 85),(8,old 86),(9,old 87),
   (10,old 94),(11,old 89),(12,old 90),(13,old 127),(14,old 127),(15,old 90),
   (16,old 127),(17,old 88),(18,old 126),(19,old 87),(20,old 126),(97,2)]

def ttReverseLiftSetupNaturalPrefix (old : Fin 128 → ℕ) (count : ℕ) : Fin 128 → ℕ :=
  ((ttReverseLiftSetupCells old).take count).foldl
    (fun regs cell => Function.update regs cell.1 cell.2) old

def ttReverseLiftSetupMiddle (s : State ttProgram) (count label : ℕ) (hl : label<512) : State ttProgram where
  label := (⟨label,hl⟩ : Fin 512)
  real := s.real
  natural := ttReverseLiftSetupNaturalPrefix s.natural count
  memory := s.memory
  status := .running

def ttReverseLiftSetupEnd (s : State ttProgram) : State ttProgram :=
  ttReverseLiftSetupMiddle (ttReverseLiftDataState s) 18 11 (by decide)

 theorem ttReverseLift_setup_six (s : State ttProgram) (hl : s.label=322) (hs : s.status=.running) :
    (ordinaryStep ttProgram)^[6] s=ttReverseLiftSetupMiddle s 6 328 (by decide) := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,ttReverseLift_labels,Function.iterate_succ_apply',ordinaryStep,hl,hs,
    ttProgram_code_reverse_322,ttProgram_code_reverse_323,ttProgram_code_reverse_324,
    ttProgram_code_reverse_325,ttProgram_code_reverse_326,ttProgram_code_reverse_327,
    ttReverseLiftSetupMiddle,ttReverseLiftSetupNaturalPrefix,ttReverseLiftSetupCells,List.foldl]

 theorem ttReverseLift_setup_twelve (s : State ttProgram) :
    (ordinaryStep ttProgram)^[6] (ttReverseLiftSetupMiddle s 6 328 (by decide))=
      ttReverseLiftSetupMiddle s 12 334 (by decide) := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,ttReverseLift_labels,Function.iterate_succ_apply',ordinaryStep,
    ttProgram_code_reverse_328,ttProgram_code_reverse_329,ttProgram_code_reverse_330,
    ttProgram_code_reverse_331,ttProgram_code_reverse_332,ttProgram_code_reverse_333,
    ttReverseLiftSetupMiddle,ttReverseLiftSetupNaturalPrefix,ttReverseLiftSetupCells,List.foldl]

 theorem ttReverseLift_setup_eighteen (s : State ttProgram) :
    (ordinaryStep ttProgram)^[6] (ttReverseLiftSetupMiddle s 12 334 (by decide))=
      ttReverseLiftSetupMiddle s 18 340 (by decide) := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,ttReverseLift_labels,Function.iterate_succ_apply',ordinaryStep,
    ttProgram_code_reverse_334,ttProgram_code_reverse_335,ttProgram_code_reverse_336,
    ttProgram_code_reverse_337,ttProgram_code_reverse_338,ttProgram_code_reverse_339,
    ttReverseLiftSetupMiddle,ttReverseLiftSetupNaturalPrefix,ttReverseLiftSetupCells,List.foldl]

 theorem ttReverseLift_setup_jump (s : State ttProgram) :
    ordinaryStep ttProgram (ttReverseLiftSetupMiddle s 18 340 (by decide))=
      ttReverseLiftSetupMiddle s 18 11 (by decide) := by
  rfl

 theorem ttReverseLift_setup_steps (s : State ttProgram) (hl : s.label=319) (hs : s.status=.running) :
    (ordinaryStep ttProgram)^[22] s=ttReverseLiftSetupEnd s := by
  rw [show 22=19+3 by omega,Function.iterate_add_apply,ttReverseLift_data_steps s hl hs]
  rw [show 19=1+(6+(6+6)) by omega,Function.iterate_add_apply,
    Function.iterate_add_apply,Function.iterate_add_apply,
    ttReverseLift_setup_six (ttReverseLiftDataState s) rfl rfl,
    ttReverseLift_setup_twelve (ttReverseLiftDataState s),
    ttReverseLift_setup_eighteen (ttReverseLiftDataState s)]
  exact ttReverseLift_setup_jump (ttReverseLiftDataState s)

def ttReverseLiftReturnEnd (s : State ttProgram) : State ttProgram where
  label := if s.natural 84=0 then 349 else 287
  real := s.real
  natural := Function.update (Function.update (Function.update (Function.update s.natural
    (89 : Fin 128) (s.natural 90)) (90 : Fin 128) (s.natural 89))
    (84 : Fin 128) (s.natural 84-1)) (123 : Fin 128)
    (if s.natural 84=0 then s.natural 71+s.natural 76*s.natural 64 else s.natural 89)
  memory := s.memory
  status := .running

 theorem ttReverseLift_return_steps (s : State ttProgram) (hl : s.label=32) (hs : s.status=.running)
    (htag : s.natural 97=2) (hz : s.natural 127=0) (ho : s.natural 126=1) :
    (ordinaryStep ttProgram)^[8] s=ttReverseLiftReturnEnd s := by
  by_cases h : s.natural 84=0
  all_goals apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,ttReverseLift_labels,Function.iterate_succ_apply',ordinaryStep,hl,hs,htag,hz,ho,h,
    ttProgram_code_matrix_exit,ttProgram_code_forward_394,ttProgram_code_reverse_341,
    ttProgram_code_reverse_342,ttProgram_code_reverse_343,ttProgram_code_reverse_344,
    ttProgram_code_reverse_345,ttProgram_code_reverse_346,ttProgram_code_reverse_347,
    ttProgram_code_reverse_348,ttReverseLiftReturnEnd,Function.update_idem,ttReverseLift_naturals]

  all_goals funext i
  all_goals by_cases hi84 : i=(84 : Fin 128)
  all_goals by_cases hi123 : i=(123 : Fin 128)
  all_goals by_cases hi89 : i=(89 : Fin 128)
  all_goals by_cases hi90 : i=(90 : Fin 128)
  all_goals simp_all (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.update_apply]
  all_goals have hi : i=(84 : Fin 128) := Fin.ext hi84
  all_goals simpa only [hi] using h

#assert_trust kernel ttReverseLift_setup_steps
#assert_trust kernel ttReverseLift_return_steps
#print axioms ttReverseLift_setup_steps
#print axioms ttReverseLift_return_steps
end NLA.Proofs.TR04
