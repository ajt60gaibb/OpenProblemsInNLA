import NLA.Proofs.TR04.MachineTTHeaderDispatch
import NLA.Proofs.TR04.TTMemoryLayout

/-! Four metadata cells are written by the literal cast/write/increment code.
The finite-prefix memory below is a proved poststate of those instructions. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout

local instance ttMetadata_nonzero_realRegisters : NeZero ttProgram.realRegisters :=
  ⟨by change (16 : ℕ) ≠ 0; decide⟩

theorem ttProgram_code_metadata_241 : ttProgram.code 241 = .mulNat 93 125 84 242 := rfl
theorem ttProgram_code_metadata_242 : ttProgram.code 242 = .addNat 93 68 93 243 := rfl
theorem ttProgram_code_metadata_243 : ttProgram.code 243 = .castNat 13 85 244 := rfl
theorem ttProgram_code_metadata_244 : ttProgram.code 244 = .write 93 13 245 := rfl
theorem ttProgram_code_metadata_245 : ttProgram.code 245 = .increment 93 246 := rfl
theorem ttProgram_code_metadata_246 : ttProgram.code 246 = .castNat 13 86 247 := rfl
theorem ttProgram_code_metadata_247 : ttProgram.code 247 = .write 93 13 248 := rfl
theorem ttProgram_code_metadata_248 : ttProgram.code 248 = .increment 93 249 := rfl
theorem ttProgram_code_metadata_249 : ttProgram.code 249 = .castNat 13 87 250 := rfl
theorem ttProgram_code_metadata_250 : ttProgram.code 250 = .write 93 13 251 := rfl
theorem ttProgram_code_metadata_251 : ttProgram.code 251 = .increment 93 252 := rfl
theorem ttProgram_code_metadata_252 : ttProgram.code 252 = .castNat 13 88 253 := rfl
theorem ttProgram_code_metadata_253 : ttProgram.code 253 = .write 93 13 254 := rfl
theorem ttProgram_code_metadata_254 : ttProgram.code 254 = .increment 93 255 := rfl

 def ttMetadataCell (s : State ttProgram) (field : ℕ) : ℝ :=
  if h : field < 4 then (s.natural (⟨85 + field, by omega⟩ : Fin 128) : ℝ) else 0

 def ttMetadataState (s : State ttProgram) (base count : ℕ) (hc : count ≤ 4) : State ttProgram where
  label := (⟨243 + 3 * count, by omega⟩ : Fin 512)
  real := if count = 0 then s.real else Function.update s.real (⟨13, by decide⟩ : Fin 16) (ttMetadataCell s (count - 1))
  natural := Function.update s.natural 93 (base + count)
  memory := prefixMemory s.memory (ttMetadataCell s) base count
  status := .running

 theorem ttMetadata_setup (s : State ttProgram) (L : Layout) (level : ℕ)
    (hl : s.label = 241) (hs : s.status = .running)
    (hmeta : s.natural 68 = L.metadata) (hfour : s.natural 125 = 4)
    (hlevel : s.natural 84 = level) :
    (ordinaryStep ttProgram)^[2] s = ttMetadataState s (L.metadata + 4 * level) 0 (by decide) := by
  have hu68 : Function.update s.natural 93 (4 * level) 68 = L.metadata := by
    rw [Function.update_of_ne (by decide)]
    exact hmeta
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Function.iterate_succ_apply',ordinaryStep,
    hl,hs,hu68,hfour,hlevel,ttProgram_code_metadata_241,ttProgram_code_metadata_242,ttMetadataState,
    prefixMemory_zero,Function.update_idem]

 theorem ttMetadata_cell_steps (s : State ttProgram) (base : ℕ) (field : Fin 4) :
    (ordinaryStep ttProgram)^[3] (ttMetadataState s base field.val (by have := field.isLt; omega)) =
      ttMetadataState s base (field.val + 1) (by have := field.isLt; omega) := by
  have hu85 (v : ℕ) : Function.update s.natural 93 v 85 = s.natural 85 :=
    Function.update_of_ne (by decide) _ _
  have hu86 (v : ℕ) : Function.update s.natural 93 v 86 = s.natural 86 :=
    Function.update_of_ne (by decide) _ _
  have hu87 (v : ℕ) : Function.update s.natural 93 v 87 = s.natural 87 :=
    Function.update_of_ne (by decide) _ _
  have hu88 (v : ℕ) : Function.update s.natural 93 v 88 = s.natural 88 :=
    Function.update_of_ne (by decide) _ _
  fin_cases field
  all_goals apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Function.iterate_succ_apply',ordinaryStep,
    ttProgram_code_metadata_243, ttProgram_code_metadata_244, ttProgram_code_metadata_245, ttProgram_code_metadata_246, ttProgram_code_metadata_247, ttProgram_code_metadata_248, ttProgram_code_metadata_249, ttProgram_code_metadata_250, ttProgram_code_metadata_251, ttProgram_code_metadata_252, ttProgram_code_metadata_253, ttProgram_code_metadata_254,ttMetadataState,ttMetadataCell,
    Function.update_idem,prefixMemory_zero]
  all_goals simp only [hu85,hu86,hu87,hu88]
  all_goals first
    | simpa [prefixMemory_zero,ttMetadataCell] using prefixMemory_update s.memory (ttMetadataCell s) base 0
    | exact prefixMemory_update s.memory (ttMetadataCell s) base 1
    | exact prefixMemory_update s.memory (ttMetadataCell s) base 2
    | exact prefixMemory_update s.memory (ttMetadataCell s) base 3

 theorem ttMetadata_cells_prefix (s : State ttProgram) (base count : ℕ) (hc : count ≤ 4) :
    (ordinaryStep ttProgram)^[3 * count] (ttMetadataState s base 0 (by decide)) =
      ttMetadataState s base count hc := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have hk : count < 4 := by omega
    rw [show 3*(count+1)=3+3*count by omega,Function.iterate_add_apply,ih (by omega)]
    exact ttMetadata_cell_steps s base ⟨count,hk⟩

 theorem ttMetadata_steps (s : State ttProgram) (L : Layout) (level : ℕ)
    (hl : s.label = 241) (hs : s.status = .running)
    (hmeta : s.natural 68 = L.metadata) (hfour : s.natural 125 = 4)
    (hlevel : s.natural 84 = level) :
    (ordinaryStep ttProgram)^[14] s = ttMetadataState s (L.metadata + 4 * level) 4 (by decide) := by
  rw [show 14 = 12 + 2 by omega,Function.iterate_add_apply,
    ttMetadata_setup s L level hl hs hmeta hfour hlevel]
  exact ttMetadata_cells_prefix s _ 4 (by decide)

 theorem ttMetadata_run_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (L : Layout) (level : ℕ)
    (hl : (trace.state offset).label = 241) (hs : (trace.state offset).status = .running)
    (hmeta : (trace.state offset).natural 68 = L.metadata)
    (hfour : (trace.state offset).natural 125 = 4)
    (hlevel : (trace.state offset).natural 84 = level) :
    trace.state (offset + 14) = ttMetadataState (trace.state offset) (L.metadata + 4 * level) 4 (by decide) ∧
      CostThrough ttProgram trace (offset + 14) ≤ CostThrough ttProgram trace offset + 14 := by
  have he := ttMetadata_steps (trace.state offset) L level hl hs hmeta hfour hlevel
  have hn : ((ordinaryStep ttProgram)^[14] (trace.state offset)).status = .running := by rw [he]; rfl
  obtain ⟨hv,hc⟩ := trace_scalar_block_at ht offset 14
    (fun j hj _ => ttOrdinary_nosvd_prefix_of_running _ _ hn j hj)
  exact ⟨hv.trans he,hc⟩

theorem ttMetadata_final_cell (s : State ttProgram) (base : ℕ) (field : Fin 4) :
    (ttMetadataState s base 4 (by decide)).memory (base + field.val) =
      (s.natural (⟨85 + field.val,by have := field.isLt;omega⟩ : Fin 128) : ℝ) := by
  have hm : base ≤ base + field.val ∧ base + field.val < base + 4 := by have := field.isLt; omega
  have hd : base + field.val - base = field.val := by omega
  simp only [ttMetadataState,prefixMemory,if_pos hm,hd,ttMetadataCell,dif_pos field.isLt]

theorem ttMetadata_fields_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (L : Layout) (level : ℕ)
    (hl : (trace.state offset).label = 241) (hs : (trace.state offset).status = .running)
    (hmeta : (trace.state offset).natural 68 = L.metadata)
    (hfour : (trace.state offset).natural 125 = 4)
    (hlevel : (trace.state offset).natural 84 = level) :
    (trace.state (offset+14)).label = 255 ∧
    (trace.state (offset+14)).status = .running ∧
    (trace.state (offset+14)).natural 93 = L.metadata+4*level+4 ∧
    (∀ field : Fin 4, (trace.state (offset+14)).memory (L.metadataCell level field.val) =
      ((trace.state offset).natural (⟨85+field.val,by have := field.isLt;omega⟩ : Fin 128) : ℝ)) ∧
    (∀ address, ¬(L.metadata+4*level ≤ address ∧ address < L.metadata+4*level+4) →
      (trace.state (offset+14)).memory address = (trace.state offset).memory address) ∧
    (∀ i : Fin 128, i ≠ 93 → (trace.state (offset+14)).natural i = (trace.state offset).natural i) ∧
    (∀ i : Fin 16, i ≠ 13 → (trace.state (offset+14)).real i = (trace.state offset).real i) ∧
    CostThrough ttProgram trace (offset+14) ≤ CostThrough ttProgram trace offset+14 := by
  obtain ⟨he,hc⟩ := ttMetadata_run_at ht offset L level hl hs hmeta hfour hlevel
  refine ⟨?_,?_,?_,?_,?_,?_,?_,hc⟩
  · rw [he]; rfl
  · rw [he]; rfl
  · rw [he]
    change Function.update (trace.state offset).natural 93 (L.metadata+4*level+4) 93 = L.metadata+4*level+4
    exact Function.update_self _ _ _
  · intro field
    rw [he]
    exact ttMetadata_final_cell _ _ field
  · intro address ha
    rw [he]
    exact prefixMemory_outside _ _ _ _ _ ha
  · intro i hi
    rw [he]
    exact Function.update_of_ne hi _ _
  · intro i hi
    rw [he]
    exact Function.update_of_ne hi _ _

#assert_trust kernel ttMetadata_fields_at
#print axioms ttMetadata_fields_at
#assert_trust kernel ttMetadata_steps
#assert_trust kernel ttMetadata_run_at
#print axioms ttMetadata_steps
#print axioms ttMetadata_run_at
end NLA.Proofs.TR04
