import NLA.Proofs.TR04.MachineTTReverseLift

/-! Actual strided frame lift through the installed matrix bank and reverse
return. Every output cell is the literal finite tensor contraction with Q. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat
private theorem ttReverseLiftCall_naturals : ttProgram.extraNatRegisters=127 := rfl

structure TTReverseLiftRegisters (s : State ttProgram)
    (m q cols stride frame input output : ℕ) : Prop where
  zero : s.natural 127=0
  one : s.natural 126=1
  rows : s.natural 85=m
  width : s.natural 86=q
  columns : s.natural 87=cols
  rowStride : s.natural 2=stride
  frameBase : s.natural 67+s.natural 84*s.natural 66=frame
  inputBase : s.natural 89=input
  outputBase : s.natural 90=output

 theorem ttReverseLiftSetup_relates (s : State ttProgram)
    (m q : ℕ) (ns : List ℕ) (stride frame input output : ℕ)
    (hr : TTReverseLiftRegisters s m q (suffixSize ns) stride frame input output) :
    ttMatrixEmbedding.Relates (matrixMultiplyRowState
      (liftMultiplyData s.memory m q ns frame stride input output) 0 (ttForwardScratch s))
      (ttReverseLiftSetupEnd s) := by
  rcases hr with ⟨hz,ho,hm,hq,hcols,hstride,hframe,hinput,houtput⟩
  constructor
  · rfl
  · funext i
    rfl
  · funext i
    change ((ttReverseLiftSetupCells (ttReverseLiftDataState s).natural).take 18).foldl
      (fun regs cell => Function.update regs cell.1 cell.2) (ttReverseLiftDataState s).natural
      (⟨4+i.val,by have := i.isLt;change i.val<17 at this;omega⟩ : Fin 128) = _
    fin_cases i
    all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,ttReverseLiftSetupCells,List.foldl,ttReverseLiftDataState,
      matrixMultiplyRowState,matrixMultiplyState,liftMultiplyData,actMultiplyData,
      ttForwardScratch,ttReverseLiftCall_naturals,hz,ho,hm,hq,hcols,hstride,hframe,hinput,houtput]
  · simp only [ttReverseLiftSetupEnd,ttReverseLiftSetupMiddle,ttReverseLiftDataState,
      matrixMultiplyRowState,matrixMultiplyState,MatrixMultiplyData.outputPrefix,
      Nat.zero_mul,prefixMemory_zero,liftMultiplyData,actMultiplyData]
  · rfl

def TTReverseLiftSetupStable (i : Fin 128) : Prop :=
  ((i.val < 4) ∨ (21 ≤ i.val)) ∧ i≠88 ∧ i≠94 ∧ i≠97

 theorem ttReverseLiftSetup_natural_outside (s : State ttProgram) (i : Fin 128)
    (hi : TTReverseLiftSetupStable i) : (ttReverseLiftSetupEnd s).natural i=s.natural i := by
  rcases hi with ⟨hi,h88,h94,h97⟩
  have hfold : (ttReverseLiftSetupEnd s).natural i=(ttReverseLiftDataState s).natural i := by
    apply ttNaturalFold_outside
    intro cell hc
    have hc' := List.mem_of_mem_take hc
    simp only [ttReverseLiftSetupCells,List.mem_cons,List.not_mem_nil,or_false] at hc'
    have hne (j : Fin 128) (hj : 4≤j.val ∧ j.val≤20) : i≠j := by
      intro heq
      have he := congrArg Fin.val heq
      omega
    rcases hc' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact h97 | exact hne _ (by dsimp only [Prod.fst];decide)
  rw [hfold]
  simp only [ttReverseLiftDataState,Function.update_of_ne h88,Function.update_of_ne h94]

 theorem ttReverseLiftSetup_tag (s : State ttProgram) :
    (ttReverseLiftSetupEnd s).natural 97=2 := by
  simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,-Fin.val_eq_zero_iff,
    ttReverseLiftSetupEnd,ttReverseLiftSetupMiddle,ttReverseLiftSetupNaturalPrefix,ttReverseLiftSetupCells,List.foldl]

 theorem ttReverseLiftSetup_fields (s : State ttProgram) :
    (ttReverseLiftSetupEnd s).natural 88=s.natural 2 ∧
    (ttReverseLiftSetupEnd s).natural 94=s.natural 67+s.natural 84*s.natural 66 := by
  simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,-Fin.val_eq_zero_iff,
    Fin.ext_iff,ttReverseLiftSetupEnd,ttReverseLiftSetupMiddle,ttReverseLiftSetupNaturalPrefix,ttReverseLiftSetupCells,List.foldl,
    ttReverseLiftDataState,ttReverseLiftCall_naturals]

 theorem ttReverse_lift_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (m q : ℕ) (ns : List ℕ) (stride frame input output : ℕ)
    (hl : (trace.state offset).label=319) (hs : (trace.state offset).status=.running)
    (hr : TTReverseLiftRegisters (trace.state offset) m q (suffixSize ns) stride frame input output)
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (A : Tensor (q::ns)) (hA : StoresTensor (trace.state offset).memory input (q::ns) A)
    (hQblock : DisjointBlocks frame (m*stride) output (m*suffixSize ns))
    (hAblock : DisjointBlocks input (q*suffixSize ns) output (m*suffixSize ns)) :
    let p := liftMultiplyData (trace.state offset).memory m q ns frame stride input output
    let time := offset+22+matrixMultiplyReturnTime p
    (trace.state time).label=32 ∧ (trace.state time).status=.running ∧
    StoresTensor (trace.state time).memory output (m::ns) (lift Q A) ∧
    StoresTensor (trace.state time).memory input (q::ns) A ∧
    StoresFrame (trace.state time).memory frame stride Q ∧
    (∀ a, ¬(output≤a ∧ a<output+m*suffixSize ns) →
      (trace.state time).memory a=(trace.state offset).memory a) ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+22+17*(m+q+suffixSize ns+1)^3 ∧
    (∀ i : Fin 16, ((i.val < 2) ∨ (5 ≤ i.val)) → (trace.state time).real i=(trace.state offset).real i) ∧
    (∀ i : Fin 128, TTReverseLiftSetupStable i →
      (trace.state time).natural i=(trace.state offset).natural i) ∧
    (trace.state time).natural 97=2 ∧
    (trace.state time).natural 88=stride ∧ (trace.state time).natural 94=frame := by
  let s := trace.state offset
  let p := liftMultiplyData s.memory m q ns frame stride input output
  obtain ⟨hsetup,hsetupCost⟩ := ttScalar_finish_at ht offset 22 (ttReverseLiftSetupEnd s)
    (ttReverseLift_setup_steps s hl hs) rfl
  have hc : ttMatrixEmbedding.Relates (matrixMultiplyRowState p 0 (ttForwardScratch s))
      (trace.state (offset+22)) := by
    rw [hsetup];exact ttReverseLiftSetup_relates s m q ns stride frame input output hr
  obtain ⟨hp,hstatus,hout,hin,hframe,hmem,hcost,hreal,hnatural⟩ :=
    ttMatrixEmbedding.lift_run_at s.memory frame stride input output hq Q hQ A hA
      hQblock hAblock (ttForwardScratch s) ht (offset+22) hc
  refine ⟨hp,hstatus,hout,hin,hframe,hmem,?_,?_,?_,?_,?_,?_⟩
  · exact hcost.trans (Nat.add_le_add_right hsetupCost _)
  · intro i hi
    rw [hreal i (ttMatrix_real_outside i hi),hsetup]
    rfl
  · intro i hi
    rw [hnatural i (ttMatrix_natural_outside i hi.1),hsetup]
    exact ttReverseLiftSetup_natural_outside s i hi
  · rw [hnatural 97 (ttMatrix_natural_outside 97 (by decide)),hsetup,ttReverseLiftSetup_tag]
  · rw [hnatural 88 (ttMatrix_natural_outside 88 (by decide)),hsetup,(ttReverseLiftSetup_fields s).1]
    exact hr.rowStride
  · rw [hnatural 94 (ttMatrix_natural_outside 94 (by decide)),hsetup,(ttReverseLiftSetup_fields s).2]
    exact hr.frameBase

def TTReverseReturnStable (i : Fin 128) : Prop := i≠89 ∧ i≠90 ∧ i≠84 ∧ i≠123

 theorem ttReverseLiftReturnEnd_natural (s : State ttProgram) (i : Fin 128)
    (hi : TTReverseReturnStable i) : (ttReverseLiftReturnEnd s).natural i=s.natural i := by
  rcases hi with ⟨h89,h90,h84,h123⟩
  simp only [ttReverseLiftReturnEnd,Function.update_of_ne h89,Function.update_of_ne h90,
    Function.update_of_ne h84,Function.update_of_ne h123]

 theorem ttReverseLiftReturnEnd_fields (s : State ttProgram) :
    (ttReverseLiftReturnEnd s).label=(if s.natural 84=0 then 349 else 287) ∧
    (ttReverseLiftReturnEnd s).status=.running ∧
    (ttReverseLiftReturnEnd s).natural 89=s.natural 90 ∧
    (ttReverseLiftReturnEnd s).natural 90=s.natural 89 ∧
    (ttReverseLiftReturnEnd s).natural 84=s.natural 84-1 ∧
    (ttReverseLiftReturnEnd s).memory=s.memory ∧ (ttReverseLiftReturnEnd s).real=s.real ∧
    (s.natural 84=0 → (ttReverseLiftReturnEnd s).natural 123=s.natural 71+s.natural 76*s.natural 64) := by
  simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,-Fin.val_eq_zero_iff,
    Fin.ext_iff,ttReverseLiftReturnEnd,ttReverseLiftCall_naturals]
  intro h hn
  exact (hn h).elim

 theorem ttReverseLift_return_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label=32) (hs : (trace.state offset).status=.running)
    (htag : (trace.state offset).natural 97=2) (hz : (trace.state offset).natural 127=0)
    (ho : (trace.state offset).natural 126=1) :
    trace.state (offset+8)=ttReverseLiftReturnEnd (trace.state offset) ∧
    CostThrough ttProgram trace (offset+8)≤CostThrough ttProgram trace offset+8 := by
  exact ttScalar_finish_at ht offset 8 _
    (ttReverseLift_return_steps _ hl hs htag hz ho) rfl

#assert_trust kernel ttReverseLiftReturnEnd_natural
#assert_trust kernel ttReverseLiftReturnEnd_fields
#assert_trust kernel ttReverseLift_return_at

#assert_trust kernel ttReverseLiftSetup_relates
#assert_trust kernel ttReverseLiftSetup_natural_outside
#assert_trust kernel ttReverseLiftSetup_tag
#assert_trust kernel ttReverseLiftSetup_fields
#assert_trust kernel ttReverse_lift_at
#print axioms ttReverse_lift_at
end NLA.Proofs.TR04
