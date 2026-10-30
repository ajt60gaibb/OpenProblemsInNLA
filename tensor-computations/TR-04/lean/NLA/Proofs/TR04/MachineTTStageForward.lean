import NLA.Proofs.TR04.MachineTTStageMetadata

/-! One actual metadata/forward phase with its saved parent data. First-source
and child-source branches share the same stored child and protection result. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat

 theorem TTReverseMetadata.memory_eq {memory memory' : ℕ → ℝ} {base m q cols stride : ℕ}
    (h : TTReverseMetadata memory base m q cols stride)
    (he : ∀ a,base≤a ∧ a<base+4 → memory' a=memory a) :
    TTReverseMetadata memory' base m q cols stride := by
  constructor
  · rw [he base (by omega)];exact h.rows
  · rw [he (base+1) (by omega)];exact h.width
  · rw [he (base+2) (by omega)];exact h.columns
  · rw [he (base+3) (by omega)];exact h.rowStride

structure TTStageForwardResult (old final : State ttProgram) (L : Layout) (level m q n : ℕ)
    (ns : List ℕ) (Q : Matrix (Fin m) (Fin q) ℝ) (A : Tensor (m::n::ns)) : Prop where
  label : final.label=(if level+1<L.order-1 then 208 else 286)
  running : final.status=.running
  levelValue : final.natural 84=level+1
  previousRank : final.natural 100=q
  currentStored : StoresTensor final.memory (final.natural 89) ((q*n)::ns) (merge q n ns (contract Q A))
  frameStored : StoresFrame final.memory (L.frame level) (old.natural 88) Q
  metadataStored : TTReverseMetadata final.memory (L.metadata+4*level) m q (suffixSize (n::ns)) (old.natural 88)
  workPair : TTWorkPair L final
  preserves : TTStagePreserves L level old final
  allocation : TTAllocationRegisters L final

 theorem ttStageForward_pack {old middle final : State ttProgram}
    (L : Layout) (level m q n : ℕ) (ns : List ℕ)
    (Q : Matrix (Fin m) (Fin q) ℝ) (A : Tensor (m::n::ns))
    (hmiddle : TTStageData L level m q (n::ns) Q A middle)
    (hmeta : TTReverseMetadata middle.memory (L.metadata+4*level) m q (suffixSize (n::ns)) (old.natural 88))
    (hpres : TTStagePreserves L level old middle)
    (hlevel : level<L.order) (hcount : q*suffixSize (n::ns)≤L.entries)
    (next : ℕ)
    (h : TTForwardResult middle final m q (n::ns) (old.natural 88) (L.frame level)
      (middle.natural 89) (middle.natural 90) next Q A)
    (hp : TTWorkPair L final) : TTStageForwardResult old final L level m q n ns Q A := by
  have hout := hmiddle.buffers.output_choice
  have hbefore : L.metadata+4*level+4≤middle.natural 90 := by
    have hm : L.metadata+4*level+4≤L.workA := by unfold Layout.workA;omega
    rcases hout with ho|ho <;> rw [ho]
    · exact hm
    · unfold Layout.workB;omega
  have hmetaD : DisjointBlocks (L.metadata+4*level) 4 (middle.natural 90) (q*suffixSize (n::ns)) :=
    disjoint_of_end_le hbefore
  have hp' := ttStagePreserves_trans hpres (h.stagePreserves L level hlevel hout hcount)
  constructor
  · rw [h.label,hmiddle.levelValue,hmiddle.allocation.order]
  · exact h.running
  · rw [h.level,hmiddle.levelValue]
  · exact h.previousRank
  · exact h.mergedStored
  · exact h.frameStored
  · exact hmeta.memory_eq (h.metadata _ 4 hmetaD)
  · exact hp
  · exact hp'
  · exact ttStagePreserves_allocation (h.stagePreserves L level hlevel hout hcount) hmiddle.allocation

 theorem ttStage_forward_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (L : Layout) (level m q n : ℕ) (ns : List ℕ)
    (Q : Matrix (Fin m) (Fin q) ℝ) (A : Tensor (m::n::ns))
    (hl : (trace.state offset).label=241) (hs : (trace.state offset).status=.running)
    (hd : TTStageData L level m q (n::ns) Q A (trace.state offset))
    (hlevel : level<L.order) (hqm : q≤m) (hm : m≤L.entries)
    (hc : m*suffixSize (n::ns)≤L.entries) :
    ∃ elapsed : ℕ,elapsed≤44+17*(m+q+suffixSize (n::ns)+1)^3 ∧
      TTStageForwardResult (trace.state offset) (trace.state (offset+elapsed)) L level m q n ns Q A ∧
      CostThrough ttProgram trace (offset+elapsed)≤CostThrough ttProgram trace offset+
        44+17*(m+q+suffixSize (n::ns)+1)^3 := by
  let s := trace.state offset
  let middle := trace.state (offset+14)
  obtain ⟨hlabel,hstatus,hd',hmeta,hpres,hn,hmetaCost⟩ :=
    ttStage_metadata_at ht offset L level m q (n::ns) Q A hl hs hd hlevel hqm hm hc
  have hcount : q*suffixSize (n::ns)≤L.entries := (Nat.mul_le_mul_right _ hqm).trans hc
  obtain ⟨hqs,hstride⟩ := hd.stride_bounds hqm hm
  have hQ : StoresFrame middle.memory (L.frame level) (s.natural 88) Q := by
    have hh := hd'.frameStored
    rw [hn 88 (by decide)] at hh
    exact hh
  have hQblock := ttFrame_output_disjoint L level hlevel m (s.natural 88) (middle.natural 90)
    (q*suffixSize (n::ns)) hm hstride hd'.buffers.output_choice hcount
  have hAblock := hd'.buffers.input_output_disjoint _ _ hc hcount
  have hregs (tag : ℕ) (htag : middle.natural 108=tag) :
      TTForwardRegisters middle m q (suffixSize (n::ns)) (s.natural 88) (L.frame level)
        (middle.natural 89) (middle.natural 90) tag :=
    ⟨hd'.allocation.zero,hd'.allocation.one,hd'.rows,hd'.width,hd'.columns,hn 88 (by decide),
      hd'.frame,rfl,rfl,htag⟩
  let p := contractMultiplyData middle.memory m q (n::ns) (L.frame level) (s.natural 88)
    (middle.natural 89) (middle.natural 90)
  have hret := matrixMultiplyReturnTime_le_cubic p
  change matrixMultiplyReturnTime p≤17*(q+m+suffixSize (n::ns)+1)^3 at hret
  have hcomm : q+m+suffixSize (n::ns)+1=m+q+suffixSize (n::ns)+1 := by omega
  rw [hcomm] at hret
  rcases hd'.buffers with ⟨htag,hin,hout⟩|⟨htag,hpair⟩
  · have hw : middle.natural 69=middle.natural 90 := hd'.allocation.workA.trans hout.symm
    obtain ⟨hf,hfc⟩ := ttForward_first_at ht (offset+14) m q (n::ns) (s.natural 88) (L.frame level)
      (middle.natural 89) (middle.natural 90) hlabel hstatus (hregs 0 htag) hw hqs Q hQ A hd'.inputStored hQblock hAblock
    let elapsed := 14+19+matrixMultiplyReturnTime p+9
    have he : offset+14+19+matrixMultiplyReturnTime p+9=offset+elapsed := by dsimp [elapsed];omega
    change TTForwardResult middle (trace.state (offset+14+19+matrixMultiplyReturnTime p+9))
      m q (n::ns) (s.natural 88) (L.frame level) (middle.natural 89) (middle.natural 90)
      (middle.natural 70) Q A at hf
    rw [he] at hf hfc
    have hp : TTWorkPair L (trace.state (offset+elapsed)) :=
      Or.inl ⟨hf.current.trans hout,hf.nextBuffer.trans hd'.allocation.workB⟩
    refine ⟨elapsed,by dsimp [elapsed];omega,
      ttStageForward_pack L level m q n ns Q A hd' hmeta hpres hlevel hcount _ hf hp,?_⟩
    rw [hcomm] at hfc
    omega
  · obtain ⟨hf,hfc⟩ := ttForward_child_at ht (offset+14) m q (n::ns) (s.natural 88) (L.frame level)
      (middle.natural 89) (middle.natural 90) hlabel hstatus (hregs 1 htag) hqs Q hQ A hd'.inputStored hQblock hAblock
    let elapsed := 14+19+matrixMultiplyReturnTime p+11
    have he : offset+14+19+matrixMultiplyReturnTime p+11=offset+elapsed := by dsimp [elapsed];omega
    change TTForwardResult middle (trace.state (offset+14+19+matrixMultiplyReturnTime p+11))
      m q (n::ns) (s.natural 88) (L.frame level) (middle.natural 89) (middle.natural 90)
      (middle.natural 89) Q A at hf
    rw [he] at hf hfc
    have hp : TTWorkPair L (trace.state (offset+elapsed)) := by
      rcases hpair with ⟨hin,hout⟩|⟨hin,hout⟩
      · exact Or.inr ⟨hf.current.trans hout,hf.nextBuffer.trans hin⟩
      · exact Or.inl ⟨hf.current.trans hout,hf.nextBuffer.trans hin⟩
    refine ⟨elapsed,by dsimp [elapsed];omega,
      ttStageForward_pack L level m q n ns Q A hd' hmeta hpres hlevel hcount _ hf hp,?_⟩
    rw [hcomm] at hfc
    omega

#assert_trust kernel TTReverseMetadata.memory_eq
#assert_trust kernel TTStageForwardResult
#assert_trust kernel ttStageForward_pack
#assert_trust kernel ttStage_forward_at
#print axioms ttStage_forward_at
end NLA.Proofs.TR04
