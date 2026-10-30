import NLA.Proofs.TR04.MachineTTStageProtection
import NLA.Proofs.TR04.MachineTTInitializationTrace
import NLA.Proofs.TR04.MachineTensorMemory

/-! The actual child full-SVD instruction and its literal three-instruction
return to metadata241. Every legal full reply is permitted. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat

private theorem ttChildSVD_naturals : ttProgram.extraNatRegisters=127 := rfl
private theorem ttChildSVD_code238 : ttProgram.code 238=.copyNat 88 85 239 := rfl
private theorem ttChildSVD_code239 : ttProgram.code 239=.natural 108 1 240 := rfl
private theorem ttChildSVD_code240 : ttProgram.code 240=.jump 241 := rfl

def ttChildSVDReturnState (s : State ttProgram) : State ttProgram :=
  { s with
    label := 241
    natural := Function.update (Function.update s.natural 88 (s.natural 85)) 108 1 }

theorem ttChildSVDReturn_steps (s : State ttProgram) (hl : s.label=238)
    (hs : s.status=.running) :
    (ordinaryStep ttProgram)^[3] s=ttChildSVDReturnState s := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.update_apply,ttChildSVD_naturals,
    Function.iterate_succ_apply',ordinaryStep,hl,hs,ttChildSVDReturnState,
    ttChildSVD_code238,ttChildSVD_code239,ttChildSVD_code240]

theorem ttChild_svd_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset=s) (hl : s.label=237) (hs : s.status=.running)
    (L : Layout) (level : ℕ) (hlevel : level<L.order)
    (hrows : s.natural 85≤L.entries) (hcols : s.natural 87≤L.entries)
    (hq : s.natural 86≤s.natural 85)
    (hframe : s.natural 94=L.frame level)
    (hsigma : s.natural 103=L.childSigma) (hvbase : s.natural 104=L.childV)
    (hcurrent : L.workA≤s.natural 89) :
    ∃ U : Matrix (Fin (s.natural 85)) (Fin (s.natural 85)) ℝ,
    ∃ sigma : Fin (min (s.natural 85) (s.natural 87)) → ℝ,
    ∃ V : Matrix (Fin (s.natural 87)) (Fin (s.natural 87)) ℝ,
      ValidSVD (readMatrix s.memory (s.natural 85) (s.natural 87) (s.natural 89)) U sigma V ∧
      (trace.state (offset+4)).label=241 ∧ (trace.state (offset+4)).status=.running ∧
      (trace.state (offset+4)).natural 88=s.natural 85 ∧
      (trace.state (offset+4)).natural 108=1 ∧
      (trace.state (offset+4)).memory=
        writeSVD s.memory (L.frame level) L.childSigma L.childV U sigma V ∧
      StoresFrame (trace.state (offset+4)).memory (L.frame level) (s.natural 85)
        (U.submatrix id (Fin.castLE hq)) ∧
      (∀ address,s.natural 89≤address →
        (trace.state (offset+4)).memory address=s.memory address) ∧
      (∀ address,TTStageProtected L level address →
        (trace.state (offset+4)).memory address=s.memory address) ∧
      (∀ j : Fin 128,j≠88 → j≠108 → (trace.state (offset+4)).natural j=s.natural j) ∧
      (trace.state (offset+4)).real=s.real ∧
      CostThrough ttProgram trace (offset+4)≤CostThrough ttProgram trace offset+
        (s.natural 85+s.natural 87+1)^3+3 := by
  have hd : OutputBlocksDisjoint (s.natural 85) (s.natural 87)
      (s.natural 94) (s.natural 103) (s.natural 104) := by
    rw [hframe,hsigma,hvbase]
    exact L.child_outputs_disjoint level _ _ hrows hcols
  have hcode : ttProgram.code (trace.state offset).label=.svd 85 87 89 94 103 104 238 := by
    rw [he,hl]
    exact ttProgram_code_child_svd
  have hstatus : (trace.state offset).status=.running := he ▸ hs
  have hd' : OutputBlocksDisjoint ((trace.state offset).natural 85) ((trace.state offset).natural 87)
      ((trace.state offset).natural 94) ((trace.state offset).natural 103)
      ((trace.state offset).natural 104) := by rw [he];exact hd
  have hreply := trace_svd_at ht offset 85 87 89 94 103 104 238 hcode hstatus hd'
  rw [he] at hreply
  obtain ⟨U,sigma,V,hvalid,hnext,hcharge⟩ := hreply
  let after : State ttProgram := {s with
    label := 238
    memory := writeSVD s.memory (s.natural 94) (s.natural 103) (s.natural 104) U sigma V}
  have hnext' : trace.state (offset+1)=after := hnext
  have hsteps := ttChildSVDReturn_steps after rfl hs
  have hsteps' : (ordinaryStep ttProgram)^[3] (trace.state (offset+1))=
      ttChildSVDReturnState after := by rw [hnext'];exact hsteps
  obtain ⟨hend,hcost⟩ := ttScalar_finish_at ht (offset+1) 3 _ hsteps' hs
  have htick : offset+1+3=offset+4 := by omega
  rw [htick] at hend hcost
  have hmemory : (trace.state (offset+4)).memory=
      writeSVD s.memory (L.frame level) L.childSigma L.childV U sigma V := by
    rw [hend]
    change writeSVD s.memory (s.natural 94) (s.natural 103) (s.natural 104) U sigma V=_
    rw [hframe,hsigma,hvbase]
  have hprefixCost : CostThrough ttProgram trace (offset+1)=CostThrough ttProgram trace offset+
      (s.natural 85+s.natural 87+1)^3 := by
    simp only [CostThrough,Finset.sum_range_succ,hcharge]
  refine ⟨U,sigma,V,hvalid,?_,?_,?_,?_,hmemory,?_,?_,?_,?_,?_,by omega⟩
  · rw [hend];rfl
  · rw [hend];exact hs
  · rw [hend]
    change Function.update (Function.update s.natural 88 (s.natural 85)) 108 1 88=s.natural 85
    rw [Function.update_of_ne (by decide),Function.update_self]
  · rw [hend]
    change Function.update (Function.update s.natural 88 (s.natural 85)) 108 1 108=1
    exact Function.update_self _ _ _
  · rw [hmemory]
    exact storesFrame_prefix _ _ U hq (readMatrix_writeSVD_u s.memory _ _ _ U sigma V)
  · intro address ha
    rw [hmemory]
    exact L.write_childSVD_work level hlevel s.memory U sigma V hrows hcols address (hcurrent.trans ha)
  · intro address hp
    rw [hmemory]
    exact ttStageProtected_child_svd L level hlevel hrows hcols s.memory U sigma V address hp
  · intro j hj88 hj108
    rw [hend]
    exact (Function.update_of_ne hj108 _ _).trans (Function.update_of_ne hj88 _ _)
  · rw [hend];rfl

#assert_trust kernel ttChildSVDReturnState
#assert_trust kernel ttChildSVDReturn_steps
#assert_trust kernel ttChild_svd_at
#print axioms ttChild_svd_at
end NLA.Proofs.TR04
