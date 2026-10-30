import NLA.Proofs.TR04.MachineTTRecursiveResult

/-! Restore a saved parent from the actually completed child. The protected
prefix is a concrete memory/register relation supplied by the recursive
execution, and the reverse instructions are executed on the legal trace. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat

 theorem ttLoopKept_not_level (j : Fin 128) (hj : TTLoopKept j) : j≠84 := by
  simp only [TTLoopKept,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

 theorem ttReverseStart_preserves (L : Layout) (level : ℕ) (s : State ttProgram) :
    TTStagePreserves L level s (ttReverseStartState s) := by
  constructor
  · intro a ha;rfl
  · intro j hj
    exact Function.update_of_ne (ttLoopKept_not_level j hj) _ _

 theorem ttReverseStart_workPair {L : Layout} {s : State ttProgram} (h : TTWorkPair L s) :
    TTWorkPair L (ttReverseStartState s) := by
  have h89 : (ttReverseStartState s).natural 89=s.natural 89 := by
    change Function.update s.natural (84 : Fin 128) (s.natural 84-1) (89 : Fin 128)=_
    exact Function.update_of_ne (by decide) _ _
  have h90 : (ttReverseStartState s).natural 90=s.natural 90 := by
    change Function.update s.natural (84 : Fin 128) (s.natural 84-1) (90 : Fin 128)=_
    exact Function.update_of_ne (by decide) _ _
  rcases h with ⟨hin,hout⟩|⟨hin,hout⟩
  · exact Or.inl ⟨h89.trans hin,h90.trans hout⟩
  · exact Or.inr ⟨h89.trans hin,h90.trans hout⟩

 theorem ttStage_reverse_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (old : State ttProgram) (forwardTime readTime : ℕ)
    (L : Layout) (level m q n : ℕ) (ns : List ℕ) (r : ℕ → ℕ)
    (Q : Matrix (Fin m) (Fin q) ℝ) (A : Tensor (m::n::ns)) (Z : Tensor ((q*n)::ns))
    (hd : TTStageData L level m q (n::ns) Q A old)
    (hf : TTStageForwardResult old (trace.state forwardTime) L level m q n ns Q A)
    (hprotected : TTStagePreserves L (level+1) (trace.state forwardTime) (trace.state readTime))
    (hlabel : (trace.state readTime).label=287) (hrunning : (trace.state readTime).status=.running)
    (hreadLevel : (trace.state readTime).natural 84=level) (hpair : TTWorkPair L (trace.state readTime))
    (hZ : StoresTensor (trace.state readTime).memory ((trace.state readTime).natural 89) ((q*n)::ns) Z)
    (hcompletion : Completion ((q*n)::ns) (fun j => r (j+1)) (merge q n ns (contract Q A)) Z)
    (hlevel : level<L.order) (hqm : q≤m) (hm : m≤L.entries) (hc : m*suffixSize (n::ns)≤L.entries) :
    ∃ elapsed : ℕ,elapsed≤ttReverseMetadataTime m q (suffixSize (n::ns)) (old.natural 88)+30+
        17*(m+q+suffixSize (n::ns)+1)^3 ∧
      TTCoreResult old (trace.state (readTime+elapsed)) L level m q n ns r Q A Z ∧
      CostThrough ttProgram trace (readTime+elapsed)≤CostThrough ttProgram trace readTime+
        ttReverseMetadataTime m q (suffixSize (n::ns)) (old.natural 88)+30+
        17*(m+q+suffixSize (n::ns)+1)^3 := by
  let s := trace.state readTime
  have ha := ttStagePreserves_allocation hprotected hf.allocation
  obtain ⟨hqs,hstride⟩ := hd.stride_bounds hqm hm
  have hQ : StoresFrame s.memory (L.frame level) (old.natural 88) Q :=
    ttStagePreserves_prior_frame hprotected Q hqs hm hstride hf.frameStored
  have hmeta : TTReverseMetadata s.memory (L.metadata+4*level) m q (suffixSize (n::ns)) (old.natural 88) :=
    hf.metadataStored.memory_eq (fun a ha => hprotected.1 a (ttStageProtected_own_metadata L level a ha))
  have hmeta' : TTReverseMetadata s.memory (s.natural 68+4*s.natural 84) m q (suffixSize (n::ns))
      (old.natural 88) := by rw [ha.metadata,hreadLevel];exact hmeta
  have hregs : TTReverseRegisters s (L.frame level) (s.natural 89) (s.natural 90) := by
    constructor
    · exact ha.zero
    · exact ha.one
    · exact ha.four
    · rw [ha.frames,hreadLevel,ha.square];rfl
    · rfl
    · rfl
  have hcount : q*suffixSize (n::ns)≤L.entries := (Nat.mul_le_mul_right _ hqm).trans hc
  have hQblock := ttFrame_output_disjoint L level hlevel m (old.natural 88) (s.natural 90)
    (m*suffixSize (n::ns)) hm hstride (hpair.output_choice L s) hc
  have hZblock := hpair.disjoint L s _ _ hcount hc
  let p := liftMultiplyData s.memory m q (n::ns) (L.frame level) (old.natural 88) (s.natural 89) (s.natural 90)
  obtain ⟨hreverse,hcost⟩ := ttReverse_unmerge_at ht readTime m q n ns (old.natural 88) (L.frame level)
    (s.natural 89) (s.natural 90) hlabel hrunning hregs hmeta' hqs Q hQ Z hZ hQblock hZblock
  let elapsed := ttReverseMetadataTime m q (suffixSize (n::ns)) (old.natural 88)+22+matrixMultiplyReturnTime p+8
  have htime : readTime+ttReverseMetadataTime m q (suffixSize (n::ns)) (old.natural 88)+22+
      matrixMultiplyReturnTime p+8=readTime+elapsed := by dsimp [elapsed];omega
  rw [htime] at hreverse hcost
  have hret := matrixMultiplyReturnTime_le_cubic p
  change matrixMultiplyReturnTime p≤17*(m+q+suffixSize (n::ns)+1)^3 at hret
  have hpOldRead : TTStagePreserves L level old s :=
    ttStagePreserves_trans hf.preserves (ttStagePreserves_lower hprotected (by omega))
  have hpReverse := hreverse.stagePreserves L level hlevel (hpair.output_choice L s) hc
  have hpFull := ttStagePreserves_trans hpOldRead hpReverse
  refine ⟨elapsed,by dsimp [elapsed];omega,?_,by omega⟩
  constructor
  · exact hcompletion
  · rw [hreverse.label,hreadLevel]
  · exact hreverse.running
  · rw [hreverse.level,hreadLevel]
  · exact hreverse.currentStored
  · exact hreverse.workPair hpair
  · exact hpFull
  · exact ttStagePreserves_allocation hpFull hd.allocation
  · intro hzero
    have hz : s.natural 84=0 := hreadLevel.trans hzero
    rw [hreverse.candidatePointer hz,hpOldRead.2 71 (by unfold TTLoopKept;decide),
      hpOldRead.2 76 (by unfold TTLoopKept;decide),hpOldRead.2 64 (by unfold TTLoopKept;decide)]

#assert_trust kernel ttReverseStart_preserves
#assert_trust kernel ttReverseStart_workPair
#assert_trust kernel ttStage_reverse_at
#print axioms ttStage_reverse_at
end NLA.Proofs.TR04
