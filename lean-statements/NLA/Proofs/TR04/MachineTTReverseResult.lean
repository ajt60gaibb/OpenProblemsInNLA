import NLA.Proofs.TR04.MachineTTReverseLiftCall
import NLA.Proofs.TR04.MachineTTReverseMetadata

/-! Literal reverse matrix return: stored lift, current/next swap and actual
parent-level or completed-candidate continuation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat

def TTReverseStable (i : Fin 128) : Prop :=
  TTReverseMetadataStable i ∧ TTReverseLiftSetupStable i ∧ TTReverseReturnStable i

structure TTReverseResult (old final : State ttProgram)
    (m q : ℕ) (ns : List ℕ) (stride frame input output : ℕ)
    (Q : Matrix (Fin m) (Fin q) ℝ) (A : Tensor (q::ns)) : Prop where
  label : final.label=(if old.natural 84=0 then 349 else 287)
  running : final.status=.running
  current : final.natural 89=output
  nextBuffer : final.natural 90=input
  level : final.natural 84=old.natural 84-1
  candidatePointer : old.natural 84=0 → final.natural 123=old.natural 71+old.natural 76*old.natural 64
  frameAddress : final.natural 94=frame
  rowStride : final.natural 88=stride
  outputStored : StoresTensor final.memory output (m::ns) (lift Q A)
  inputStored : StoresTensor final.memory input (q::ns) A
  frameStored : StoresFrame final.memory frame stride Q
  memoryOutside : ∀ a, ¬(output≤a ∧ a<output+m*suffixSize ns) → final.memory a=old.memory a
  realOutside : ∀ i : Fin 16, 5 ≤ i.val → final.real i=old.real i
  naturalOutside : ∀ i : Fin 128, TTReverseStable i → final.natural i=old.natural i

 theorem TTReverseResult.currentStored {old final : State ttProgram}
    {m q : ℕ} {ns : List ℕ} {stride frame input output : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (q::ns)}
    (h : TTReverseResult old final m q ns stride frame input output Q A) :
    StoresTensor final.memory (final.natural 89) (m::ns) (lift Q A) := by
  rw [h.current];exact h.outputStored

 theorem TTReverseResult.protected {old final : State ttProgram}
    {m q : ℕ} {ns : List ℕ} {stride frame input output : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (q::ns)}
    (h : TTReverseResult old final m q ns stride frame input output Q A)
    (base count : ℕ) (hd : DisjointBlocks base count output (m*suffixSize ns)) :
    ∀ a, base≤a ∧ a<base+count → final.memory a=old.memory a := by
  intro a ha
  exact h.memoryOutside a (disjointBlocks_not_mem_right hd ha)

 theorem TTReverseResult.rebase {old mid final : State ttProgram}
    {m q : ℕ} {ns : List ℕ} {stride frame input output : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (q::ns)}
    (h : TTReverseResult mid final m q ns stride frame input output Q A)
    (hm : mid.memory=old.memory) (hl : mid.natural 84=old.natural 84)
    (hr : ∀ i : Fin 16,5 ≤ i.val → mid.real i=old.real i)
    (hn : ∀ i : Fin 128,TTReverseStable i → mid.natural i=old.natural i) :
    TTReverseResult old final m q ns stride frame input output Q A := by
  constructor
  · rw [h.label,hl]
  · exact h.running
  · exact h.current
  · exact h.nextBuffer
  · rw [h.level,hl]
  · intro hz
    have hz' : mid.natural 84=0 := hl.trans hz
    rw [h.candidatePointer hz',hn 71 (by unfold TTReverseStable TTReverseMetadataStable TTReverseLiftSetupStable TTReverseReturnStable;decide),
      hn 76 (by unfold TTReverseStable TTReverseMetadataStable TTReverseLiftSetupStable TTReverseReturnStable;decide),
      hn 64 (by unfold TTReverseStable TTReverseMetadataStable TTReverseLiftSetupStable TTReverseReturnStable;decide)]
  · exact h.frameAddress
  · exact h.rowStride
  · exact h.outputStored
  · exact h.inputStored
  · exact h.frameStored
  · intro a ha
    exact (h.memoryOutside a ha).trans (congrFun hm a)
  · intro i hi
    exact (h.realOutside i hi).trans (hr i hi)
  · intro i hi
    exact (h.naturalOutside i hi).trans (hn i hi)

 theorem ttReverse_lift_return_at {start : State ttProgram} {trace : Trace ttProgram}
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
    let time := offset+22+matrixMultiplyReturnTime p+8
    TTReverseResult (trace.state offset) (trace.state time) m q ns stride frame input output Q A ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+22+17*(m+q+suffixSize ns+1)^3+8 := by
  let s := trace.state offset
  let p := liftMultiplyData s.memory m q ns frame stride input output
  let time := offset+22+matrixMultiplyReturnTime p
  obtain ⟨hp,hstatus,hout,hin,hframe,hmem,hcost,hreal,hnatural,htag,hstride,hframeAddress⟩ :=
    ttReverse_lift_at ht offset m q ns stride frame input output hl hs hr hq Q hQ A hA hQblock hAblock
  have hn (i : Fin 128) (hi : TTReverseLiftSetupStable i) :
      (trace.state time).natural i=s.natural i := hnatural i hi
  have hz : (trace.state time).natural 127=0 :=
    (hn 127 (by unfold TTReverseLiftSetupStable;decide)).trans hr.zero
  have ho : (trace.state time).natural 126=1 :=
    (hn 126 (by unfold TTReverseLiftSetupStable;decide)).trans hr.one
  obtain ⟨he,hc⟩ := ttReverseLift_return_at ht time hp hstatus htag hz ho
  obtain ⟨hlabel,hstatus',hcurrent,hnext,hlevel,hMemory,hReal,hcopy⟩ :=
    ttReverseLiftReturnEnd_fields (trace.state time)
  refine ⟨?_,hc.trans (Nat.add_le_add_right hcost 8)⟩
  rw [he]
  constructor
  · rw [hlabel,hn 84 (by unfold TTReverseLiftSetupStable;decide)]
  · exact hstatus'
  · exact hcurrent.trans ((hn 90 (by unfold TTReverseLiftSetupStable;decide)).trans hr.outputBase)
  · exact hnext.trans ((hn 89 (by unfold TTReverseLiftSetupStable;decide)).trans hr.inputBase)
  · rw [hlevel,hn 84 (by unfold TTReverseLiftSetupStable;decide)]
  · intro hzero
    have hzero' : (trace.state time).natural 84=0 :=
      (hn 84 (by unfold TTReverseLiftSetupStable;decide)).trans hzero
    rw [hcopy hzero',hn 71 (by unfold TTReverseLiftSetupStable;decide),
      hn 76 (by unfold TTReverseLiftSetupStable;decide),hn 64 (by unfold TTReverseLiftSetupStable;decide)]
  · exact (ttReverseLiftReturnEnd_natural _ 94 (by unfold TTReverseReturnStable;decide)).trans hframeAddress
  · exact (ttReverseLiftReturnEnd_natural _ 88 (by unfold TTReverseReturnStable;decide)).trans hstride
  · rw [hMemory];exact hout
  · rw [hMemory];exact hin
  · rw [hMemory];exact hframe
  · rw [hMemory];exact hmem
  · intro i hi
    rw [hReal];exact hreal i (Or.inr hi)
  · intro i hi
    exact (ttReverseLiftReturnEnd_natural _ i hi.2.2).trans (hn i hi.2.1)

#assert_trust kernel TTReverseResult
#assert_trust kernel TTReverseResult.currentStored
#assert_trust kernel TTReverseResult.protected
#assert_trust kernel TTReverseResult.rebase
#assert_trust kernel ttReverse_lift_return_at
#print axioms ttReverse_lift_return_at
end NLA.Proofs.TR04
