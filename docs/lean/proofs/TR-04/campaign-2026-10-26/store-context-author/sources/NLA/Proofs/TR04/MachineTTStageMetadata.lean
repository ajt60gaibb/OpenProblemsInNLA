import NLA.Proofs.TR04.MachineTTRecursiveState
import NLA.Proofs.TR04.TTRecursiveDimensions

/-! The actual metadata writer preserves the stored frame and current tensor,
and writes exactly the values subsequently read by the reverse controller. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat

structure TTStageData (L : Layout) (level m q : ℕ) (ns : List ℕ)
    (Q : Matrix (Fin m) (Fin q) ℝ) (A : Tensor (m::ns)) (s : State ttProgram) : Prop where
  allocation : TTAllocationRegisters L s
  levelValue : s.natural 84=level
  rows : s.natural 85=m
  width : s.natural 86=q
  columns : s.natural 87=suffixSize ns
  frame : s.natural 94=L.frame level
  strideKind : s.natural 88=q ∨ s.natural 88=m
  frameStored : StoresFrame s.memory (L.frame level) (s.natural 88) Q
  inputStored : StoresTensor s.memory (s.natural 89) (m::ns) A
  buffers : TTStageBuffers L s

 theorem TTStageData.stride_bounds {L : Layout} {level m q : ℕ} {ns : List ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (m::ns)} {s : State ttProgram}
    (h : TTStageData L level m q ns Q A s) (hqm : q≤m) (hm : m≤L.entries) :
    q≤s.natural 88 ∧ s.natural 88≤L.entries := by
  rcases h.strideKind with hs|hs <;> rw [hs] <;> omega

 theorem TTStageBuffers.input_choice {L : Layout} {s : State ttProgram} (h : TTStageBuffers L s) :
    s.natural 89=L.input ∨ s.natural 89=L.workA ∨ s.natural 89=L.workB := by
  rcases h with ⟨_,hin,_⟩|⟨_,hp⟩
  · exact Or.inl hin
  · rcases hp with ⟨hin,_⟩|⟨hin,_⟩
    · exact Or.inr (Or.inl hin)
    · exact Or.inr (Or.inr hin)

 theorem ttStage_input_metadata_disjoint (L : Layout) (level base count : ℕ)
    (hl : level<L.order) (hb : base=L.input ∨ base=L.workA ∨ base=L.workB)
    (hc : count≤L.entries) : DisjointBlocks base count (L.metadata+4*level) 4 := by
  have hm : L.metadata+4*level+4≤L.workA := by unfold Layout.workA;omega
  rcases hb with rfl|rfl|rfl
  · apply disjoint_of_end_le
    have hi : L.input+L.entries≤L.metadata := by
      unfold Layout.metadata Layout.frames Layout.childV Layout.childSigma Layout.firstV Layout.firstSigma Layout.firstU
      omega
    omega
  · exact disjoint_symm (disjoint_of_end_le hm)
  · apply disjoint_symm
    apply disjoint_of_end_le
    unfold Layout.workB
    omega

 theorem ttStage_frame_metadata_disjoint (L : Layout) (level m stride : ℕ)
    (hl : level<L.order) (hm : m≤L.entries) (hs : stride≤L.entries) :
    DisjointBlocks (L.frame level) (m*stride) (L.metadata+4*level) 4 := by
  apply disjoint_of_end_le
  have hbefore := L.frame_before_metadata level hl
  have hcount := rectangle_capacity hm hs
  omega

 theorem ttStage_metadata_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (L : Layout) (level m q : ℕ) (ns : List ℕ)
    (Q : Matrix (Fin m) (Fin q) ℝ) (A : Tensor (m::ns))
    (hl : (trace.state offset).label=241) (hs : (trace.state offset).status=.running)
    (hd : TTStageData L level m q ns Q A (trace.state offset))
    (hlevel : level<L.order) (hqm : q≤m) (hm : m≤L.entries) (hc : m*suffixSize ns≤L.entries) :
    (trace.state (offset+14)).label=255 ∧ (trace.state (offset+14)).status=.running ∧
    TTStageData L level m q ns Q A (trace.state (offset+14)) ∧
    TTReverseMetadata (trace.state (offset+14)).memory (L.metadata+4*level) m q (suffixSize ns)
      ((trace.state offset).natural 88) ∧
    TTStagePreserves L level (trace.state offset) (trace.state (offset+14)) ∧
    (∀ j : Fin 128,j≠93 → (trace.state (offset+14)).natural j=(trace.state offset).natural j) ∧
    CostThrough ttProgram trace (offset+14)≤CostThrough ttProgram trace offset+14 := by
  let s := trace.state offset
  obtain ⟨hlabel,hstatus,hpointer,hcells,hmem,hn,hreal,hcost⟩ := ttMetadata_fields_at ht offset L level hl hs
    hd.allocation.metadata hd.allocation.four hd.levelValue
  have hp := ttMetadata_stagePreserves_at ht offset L level hlevel hl hs
    hd.allocation.metadata hd.allocation.four hd.levelValue
  obtain ⟨hqs,hstride⟩ := hd.stride_bounds hqm hm
  have hframeD := ttStage_frame_metadata_disjoint L level m (s.natural 88) hlevel hm hstride
  have hinputD := ttStage_input_metadata_disjoint L level (s.natural 89) (m*suffixSize ns)
    hlevel hd.buffers.input_choice hc
  have hQ : StoresFrame (trace.state (offset+14)).memory (L.frame level) (s.natural 88) Q := by
    apply hd.frameStored.memory_eq hqs
    intro a ha
    exact hmem a (disjointBlocks_not_mem_right hframeD ha)
  have hA : StoresTensor (trace.state (offset+14)).memory (s.natural 89) (m::ns) A := by
    apply hd.inputStored.memory_eq
    intro a ha
    apply hmem a
    apply disjointBlocks_not_mem_right hinputD
    simpa only [List.prod_cons,tensor_suffixSize_eq_prod] using ha
  have hd' : TTStageData L level m q ns Q A (trace.state (offset+14)) := by
    constructor
    · exact ttStagePreserves_allocation hp hd.allocation
    · exact (hn 84 (by decide)).trans hd.levelValue
    · exact (hn 85 (by decide)).trans hd.rows
    · exact (hn 86 (by decide)).trans hd.width
    · exact (hn 87 (by decide)).trans hd.columns
    · exact (hn 94 (by decide)).trans hd.frame
    · rw [hn 88 (by decide)];exact hd.strideKind
    · rw [hn 88 (by decide)];exact hQ
    · rw [hn 89 (by decide)];exact hA
    · have h89 := hn 89 (by decide)
      have h90 := hn 90 (by decide)
      have h108 := hn 108 (by decide)
      rcases hd.buffers with ⟨htag,hin,hout⟩|⟨htag,hpair⟩
      · exact Or.inl ⟨h108.trans htag,h89.trans hin,h90.trans hout⟩
      · apply Or.inr
        refine ⟨h108.trans htag,?_⟩
        rcases hpair with ⟨hin,hout⟩|⟨hin,hout⟩
        · exact Or.inl ⟨h89.trans hin,h90.trans hout⟩
        · exact Or.inr ⟨h89.trans hin,h90.trans hout⟩
  have hmeta : TTReverseMetadata (trace.state (offset+14)).memory (L.metadata+4*level) m q
      (suffixSize ns) (s.natural 88) := by
    constructor
    · have hv := hcells (0 : Fin 4)
      change (trace.state (offset+14)).memory (L.metadata+4*level)=((s.natural 85) : ℝ) at hv
      rwa [hd.rows] at hv
    · have hv := hcells (1 : Fin 4)
      change (trace.state (offset+14)).memory (L.metadata+4*level+1)=((s.natural 86) : ℝ) at hv
      rwa [hd.width] at hv
    · have hv := hcells (2 : Fin 4)
      change (trace.state (offset+14)).memory (L.metadata+4*level+2)=((s.natural 87) : ℝ) at hv
      rwa [hd.columns] at hv
    · exact hcells (3 : Fin 4)
  exact ⟨hlabel,hstatus,hd',hmeta,hp,hn,hcost⟩

#assert_trust kernel TTStageData
#assert_trust kernel TTStageData.stride_bounds
#assert_trust kernel ttStage_input_metadata_disjoint
#assert_trust kernel ttStage_frame_metadata_disjoint
#assert_trust kernel ttStage_metadata_at
#print axioms ttStage_metadata_at
end NLA.Proofs.TR04
