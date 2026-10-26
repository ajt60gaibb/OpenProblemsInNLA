import NLA.Proofs.TR04.MachineTTHeaderDispatch

/-! Literal setup and continuation syntax for a forward contraction call.
Every stored value below is derived from actual caller registers. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

theorem ttProgram_code_forward_255 : ttProgram.code 255 = .copyNat (⟨4,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨256,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_256 : ttProgram.code 256 = .copyNat (⟨5,by decide⟩ : Fin 128) (⟨87,by decide⟩ : Fin 128) (⟨257,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_257 : ttProgram.code 257 = .copyNat (⟨6,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨258,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_258 : ttProgram.code 258 = .copyNat (⟨7,by decide⟩ : Fin 128) (⟨86,by decide⟩ : Fin 128) (⟨259,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_259 : ttProgram.code 259 = .copyNat (⟨8,by decide⟩ : Fin 128) (⟨85,by decide⟩ : Fin 128) (⟨260,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_260 : ttProgram.code 260 = .copyNat (⟨9,by decide⟩ : Fin 128) (⟨87,by decide⟩ : Fin 128) (⟨261,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_261 : ttProgram.code 261 = .copyNat (⟨10,by decide⟩ : Fin 128) (⟨94,by decide⟩ : Fin 128) (⟨262,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_262 : ttProgram.code 262 = .copyNat (⟨11,by decide⟩ : Fin 128) (⟨89,by decide⟩ : Fin 128) (⟨263,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_263 : ttProgram.code 263 = .copyNat (⟨12,by decide⟩ : Fin 128) (⟨90,by decide⟩ : Fin 128) (⟨264,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_264 : ttProgram.code 264 = .copyNat (⟨13,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨265,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_265 : ttProgram.code 265 = .copyNat (⟨14,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨266,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_266 : ttProgram.code 266 = .copyNat (⟨15,by decide⟩ : Fin 128) (⟨90,by decide⟩ : Fin 128) (⟨267,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_267 : ttProgram.code 267 = .copyNat (⟨16,by decide⟩ : Fin 128) (⟨127,by decide⟩ : Fin 128) (⟨268,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_268 : ttProgram.code 268 = .copyNat (⟨17,by decide⟩ : Fin 128) (⟨126,by decide⟩ : Fin 128) (⟨269,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_269 : ttProgram.code 269 = .copyNat (⟨18,by decide⟩ : Fin 128) (⟨88,by decide⟩ : Fin 128) (⟨270,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_270 : ttProgram.code 270 = .copyNat (⟨19,by decide⟩ : Fin 128) (⟨87,by decide⟩ : Fin 128) (⟨271,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_271 : ttProgram.code 271 = .copyNat (⟨20,by decide⟩ : Fin 128) (⟨126,by decide⟩ : Fin 128) (⟨272,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_272 : ttProgram.code 272 = .copyNat (⟨97,by decide⟩ : Fin 128) (⟨108,by decide⟩ : Fin 128) (⟨273,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_273 : ttProgram.code 273 = .jump (⟨11,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_274 : ttProgram.code 274 = .copyNat (⟨89,by decide⟩ : Fin 128) (⟨69,by decide⟩ : Fin 128) (⟨275,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_275 : ttProgram.code 275 = .copyNat (⟨90,by decide⟩ : Fin 128) (⟨70,by decide⟩ : Fin 128) (⟨276,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_276 : ttProgram.code 276 = .jump (⟨281,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_277 : ttProgram.code 277 = .copyNat (⟨123,by decide⟩ : Fin 128) (⟨89,by decide⟩ : Fin 128) (⟨278,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_278 : ttProgram.code 278 = .copyNat (⟨89,by decide⟩ : Fin 128) (⟨90,by decide⟩ : Fin 128) (⟨279,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_279 : ttProgram.code 279 = .copyNat (⟨90,by decide⟩ : Fin 128) (⟨123,by decide⟩ : Fin 128) (⟨280,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_280 : ttProgram.code 280 = .jump (⟨281,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_281 : ttProgram.code 281 = .copyNat (⟨100,by decide⟩ : Fin 128) (⟨86,by decide⟩ : Fin 128) (⟨282,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_282 : ttProgram.code 282 = .increment (⟨84,by decide⟩ : Fin 128) (⟨283,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_283 : ttProgram.code 283 = .copyNat (⟨110,by decide⟩ : Fin 128) (⟨0,by decide⟩ : Fin 128) (⟨284,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_284 : ttProgram.code 284 = .decrement (⟨110,by decide⟩ : Fin 128) (⟨285,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_285 : ttProgram.code 285 = .lessNat (⟨84,by decide⟩ : Fin 128) (⟨110,by decide⟩ : Fin 128) (⟨208,by decide⟩ : Fin 512) (⟨286,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_286 : ttProgram.code 286 = .decrement (⟨84,by decide⟩ : Fin 128) (⟨287,by decide⟩ : Fin 512) := rfl
theorem ttProgram_code_forward_394 : ttProgram.code 394 = .equalNat (⟨97,by decide⟩ : Fin 128) (⟨126,by decide⟩ : Fin 128) (⟨277,by decide⟩ : Fin 512) (⟨341,by decide⟩ : Fin 512) := rfl

def ttForwardSetupCells (old : Fin 128 → ℕ) : List (Fin 128 × ℕ) :=
  [(4,old 127),(5,old 87),(6,old 127),(7,old 86),(8,old 85),(9,old 87),
   (10,old 94),(11,old 89),(12,old 90),(13,old 127),(14,old 127),(15,old 90),
   (16,old 127),(17,old 126),(18,old 88),(19,old 87),(20,old 126),(97,old 108)]

def ttForwardSetupNaturalPrefix (old : Fin 128 → ℕ) (count : ℕ) : Fin 128 → ℕ :=
  ((ttForwardSetupCells old).take count).foldl
    (fun registers cell => Function.update registers cell.1 cell.2) old

def ttForwardSetupMiddle (s : State ttProgram) (count label : ℕ) (hl : label < 512) : State ttProgram where
  label := (⟨label,hl⟩ : Fin 512)
  real := s.real
  natural := ttForwardSetupNaturalPrefix s.natural count
  memory := s.memory
  status := .running

def ttForwardSetupEnd (s : State ttProgram) : State ttProgram :=
  ttForwardSetupMiddle s 18 11 (by decide)

 theorem ttForwardSetup_first (s : State ttProgram) (hl : s.label = 255) (hs : s.status = .running) :
    (ordinaryStep ttProgram)^[6] s = ttForwardSetupMiddle s 6 261 (by decide) := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.iterate_succ_apply',ordinaryStep,hl,hs,
    ttProgram_code_forward_255,ttProgram_code_forward_256,ttProgram_code_forward_257,
    ttProgram_code_forward_258,ttProgram_code_forward_259,ttProgram_code_forward_260,
    ttForwardSetupMiddle,ttForwardSetupNaturalPrefix,ttForwardSetupCells,List.foldl]

 theorem ttForwardSetup_second (s : State ttProgram) :
    (ordinaryStep ttProgram)^[6] (ttForwardSetupMiddle s 6 261 (by decide)) =
      ttForwardSetupMiddle s 12 267 (by decide) := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.iterate_succ_apply',ordinaryStep,
    ttProgram_code_forward_261,ttProgram_code_forward_262,ttProgram_code_forward_263,
    ttProgram_code_forward_264,ttProgram_code_forward_265,ttProgram_code_forward_266,
    ttForwardSetupMiddle,ttForwardSetupNaturalPrefix,ttForwardSetupCells,List.foldl]

 theorem ttForwardSetup_third (s : State ttProgram) :
    (ordinaryStep ttProgram)^[6] (ttForwardSetupMiddle s 12 267 (by decide)) =
      ttForwardSetupMiddle s 18 273 (by decide) := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.iterate_succ_apply',ordinaryStep,
    ttProgram_code_forward_267,ttProgram_code_forward_268,ttProgram_code_forward_269,
    ttProgram_code_forward_270,ttProgram_code_forward_271,ttProgram_code_forward_272,
    ttForwardSetupMiddle,ttForwardSetupNaturalPrefix,ttForwardSetupCells,List.foldl]

 theorem ttForwardSetup_fourth (s : State ttProgram) :
    ordinaryStep ttProgram (ttForwardSetupMiddle s 18 273 (by decide)) = ttForwardSetupEnd s := by
  rfl

 theorem ttForwardSetup_steps (s : State ttProgram) (hl : s.label = 255) (hs : s.status = .running) :
    (ordinaryStep ttProgram)^[19] s = ttForwardSetupEnd s := by
  rw [show 19=1+(6+(6+6)) by omega,Function.iterate_add_apply,
    Function.iterate_add_apply,Function.iterate_add_apply,ttForwardSetup_first s hl hs,
    ttForwardSetup_second,ttForwardSetup_third]
  exact ttForwardSetup_fourth s

 theorem ttForwardSetup_run_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label = 255) (hs : (trace.state offset).status = .running) :
    trace.state (offset+19)=ttForwardSetupEnd (trace.state offset) ∧
      CostThrough ttProgram trace (offset+19)≤CostThrough ttProgram trace offset+19 := by
  have he := ttForwardSetup_steps (trace.state offset) hl hs
  have hn : ((ordinaryStep ttProgram)^[19] (trace.state offset)).status=.running := by rw [he]; rfl
  obtain ⟨hv,hc⟩ := trace_scalar_block_at ht offset 19
    (fun j hj _ => ttOrdinary_nosvd_prefix_of_running _ _ hn j hj)
  exact ⟨hv.trans he,hc⟩

#assert_trust kernel ttForwardSetup_steps
#assert_trust kernel ttForwardSetup_run_at
#print axioms ttForwardSetup_steps
#print axioms ttForwardSetup_run_at
end NLA.Proofs.TR04
