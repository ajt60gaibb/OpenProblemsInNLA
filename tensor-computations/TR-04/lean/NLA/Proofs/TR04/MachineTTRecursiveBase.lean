import NLA.Proofs.TR04.MachineTTStageReverse

/-! Actual two-mode base case of the recursive stage execution. The compressed
singleton is already stored, so only the literal initial decrement and saved
parent lift remain; no child solver or extra SVD is called. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat

 theorem ttCore_two_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (L : Layout) (size level m q n : ℕ) (r : ℕ → ℕ)
    (Q : Matrix (Fin m) (Fin q) ℝ) (A : Tensor [m,n])
    (hl : (trace.state offset).label=241) (hs : (trace.state offset).status=.running)
    (hd : TTStageData L level m q [n] Q A (trace.state offset))
    (hlast : level+2=L.order) (hqm : q≤m) (hm : m≤L.entries)
    (hc : m*suffixSize [n]≤L.entries) (hcols : suffixSize [n]≤L.entries) (hsize : L.entries≤size) :
    ∃ elapsed : ℕ,∃ Z : Tensor [q*n],elapsed≤2000*ttRecursiveUnit size ∧
      TTCoreResult (trace.state offset) (trace.state (offset+elapsed)) L level m q n [] r Q A Z ∧
      CostThrough ttProgram trace (offset+elapsed)≤CostThrough ttProgram trace offset+2000*ttRecursiveUnit size := by
  have hlevel : level<L.order := by omega
  obtain ⟨ef,hef,hf,hfCost⟩ := ttStage_forward_at ht offset L level m q n [] Q A hl hs hd hlevel hqm hm hc
  have hflabel : (trace.state (offset+ef)).label=286 := by
    rw [hf.label,if_neg (by omega)]
  obtain ⟨hstart,hstartCost⟩ := ttReverse_start_at ht (offset+ef) hflabel hf.running
  let readTime := offset+ef+1
  have hreadLabel : (trace.state readTime).label=287 := by rw [hstart];rfl
  have hreadRunning : (trace.state readTime).status=.running := by rw [hstart];rfl
  have hreadLevel : (trace.state readTime).natural 84=level := by
    rw [hstart]
    change Function.update (trace.state (offset+ef)).natural (84 : Fin 128)
      ((trace.state (offset+ef)).natural 84-1) (84 : Fin 128)=level
    rw [Function.update_self,hf.levelValue]
    omega
  have hpair : TTWorkPair L (trace.state readTime) := by
    rw [hstart];exact ttReverseStart_workPair hf.workPair
  have hprotected : TTStagePreserves L (level+1) (trace.state (offset+ef)) (trace.state readTime) := by
    rw [hstart];exact ttReverseStart_preserves L (level+1) _
  let Z : Tensor [q*n] := merge q n [] (contract Q A)
  have hZ : StoresTensor (trace.state readTime).memory ((trace.state readTime).natural 89) [q*n] Z := by
    rw [hstart]
    change StoresTensor (trace.state (offset+ef)).memory
      (Function.update (trace.state (offset+ef)).natural (84 : Fin 128)
        ((trace.state (offset+ef)).natural 84-1) (89 : Fin 128)) [q*n] Z
    rw [Function.update_of_ne (show (89 : Fin 128)≠84 by decide)]
    exact hf.currentStored
  have hcompletion : Completion [q*n] (fun j => r (j+1)) (merge q n [] (contract Q A)) Z :=
    Completion.single (q*n) (fun j => r (j+1)) Z
  obtain ⟨er,her,hr,hreverseCost⟩ := ttStage_reverse_at ht (trace.state offset) (offset+ef) readTime
    L level m q n [] r Q A Z hd hf hprotected hreadLabel hreadRunning hreadLevel hpair hZ
    hcompletion hlevel hqm hm hc
  rw [ttReverseMetadataTime_eq] at her hreverseCost
  have hstride := (hd.stride_bounds hqm hm).2.trans hsize
  have hb := ttRecursive_own_stage_budget size m q (suffixSize [n]) ((trace.state offset).natural 88)
    (hm.trans hsize) (hqm.trans (hm.trans hsize)) (hcols.trans hsize) hstride
  let elapsed := ef+1+er
  have htime : readTime+er=offset+elapsed := by dsimp [readTime,elapsed];omega
  rw [htime] at hr hreverseCost
  exact ⟨elapsed,Z,by dsimp [elapsed];omega,hr,by dsimp [readTime] at hreverseCost;omega⟩

#assert_trust kernel ttCore_two_at
#print axioms ttCore_two_at
end NLA.Proofs.TR04
