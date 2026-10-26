import NLA.Proofs.TR04.MachineTTReverseResult

/-! An actual complete reverse level: four real-stored metadata values are
naturally decoded, the strided frame is multiplied by the unmerged child, and
control returns to the parent read or completed-candidate copy. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat

structure TTReverseRegisters (s : State ttProgram) (frame input output : ℕ) : Prop where
  zero : s.natural 127=0
  one : s.natural 126=1
  four : s.natural 125=4
  frameBase : s.natural 67+s.natural 84*s.natural 66=frame
  inputBase : s.natural 89=input
  outputBase : s.natural 90=output

 theorem ttReverse_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (m q : ℕ) (ns : List ℕ) (stride frame input output : ℕ)
    (hl : (trace.state offset).label=287) (hs : (trace.state offset).status=.running)
    (hr : TTReverseRegisters (trace.state offset) frame input output)
    (hmetadata : TTReverseMetadata (trace.state offset).memory
      ((trace.state offset).natural 68+4*(trace.state offset).natural 84) m q (suffixSize ns) stride)
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (A : Tensor (q::ns)) (hA : StoresTensor (trace.state offset).memory input (q::ns) A)
    (hQblock : DisjointBlocks frame (m*stride) output (m*suffixSize ns))
    (hAblock : DisjointBlocks input (q*suffixSize ns) output (m*suffixSize ns)) :
    let p := liftMultiplyData (trace.state offset).memory m q ns frame stride input output
    let metadataTime := ttReverseMetadataTime m q (suffixSize ns) stride
    let time := offset+metadataTime+22+matrixMultiplyReturnTime p+8
    TTReverseResult (trace.state offset) (trace.state time) m q ns stride frame input output Q A ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+metadataTime+22+
      17*(m+q+suffixSize ns+1)^3+8 := by
  let s := trace.state offset
  let metadataTime := ttReverseMetadataTime m q (suffixSize ns) stride
  let middle := offset+metadataTime
  obtain ⟨hmetadataEnd,hmetadataCost⟩ :=
    ttReverseMetadata_run_at ht offset m q (suffixSize ns) stride hl hs hr.four hmetadata
  change trace.state middle=ttReverseMetadataEnd s m q (suffixSize ns) stride at hmetadataEnd
  have hfields := ttReverseMetadataEnd_fields s m q (suffixSize ns) stride
  rw [←hmetadataEnd] at hfields
  obtain ⟨hlabel,hstatus,hMemory,hrows,hwidth,hcols,hstride,hpointer⟩ := hfields
  have hn (i : Fin 128) (hi : TTReverseMetadataStable i) :
      (trace.state middle).natural i=s.natural i := by
    rw [hmetadataEnd];exact ttReverseMetadataEnd_natural s m q (suffixSize ns) stride i hi
  have hregs : TTReverseLiftRegisters (trace.state middle) m q (suffixSize ns) stride frame input output := by
    constructor
    · exact (hn 127 (by unfold TTReverseMetadataStable;decide)).trans hr.zero
    · exact (hn 126 (by unfold TTReverseMetadataStable;decide)).trans hr.one
    · exact hrows
    · exact hwidth
    · exact hcols
    · exact hstride
    · rw [hn 67 (by unfold TTReverseMetadataStable;decide),hn 84 (by unfold TTReverseMetadataStable;decide),
        hn 66 (by unfold TTReverseMetadataStable;decide)]
      exact hr.frameBase
    · exact (hn 89 (by unfold TTReverseMetadataStable;decide)).trans hr.inputBase
    · exact (hn 90 (by unfold TTReverseMetadataStable;decide)).trans hr.outputBase
  have hQ' : StoresFrame (trace.state middle).memory frame stride Q := by rw [hMemory];exact hQ
  have hA' : StoresTensor (trace.state middle).memory input (q::ns) A := by rw [hMemory];exact hA
  obtain ⟨hresult,hcost⟩ := ttReverse_lift_return_at ht middle m q ns stride frame input output
    hlabel hstatus hregs hq Q hQ' A hA' hQblock hAblock
  refine ⟨?_,?_⟩
  · apply hresult.rebase hMemory (hn 84 (by unfold TTReverseMetadataStable;decide))
    · intro i hi
      rw [hmetadataEnd]
      exact ttReverseMetadataEnd_real s m q (suffixSize ns) stride i (by omega)
    · intro i hi
      exact hn i hi.1
  · exact hcost.trans (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right hmetadataCost 22) _) 8)

 theorem ttReverse_unmerge_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset m q n : ℕ) (ns : List ℕ)
    (stride frame input output : ℕ)
    (hl : (trace.state offset).label=287) (hs : (trace.state offset).status=.running)
    (hr : TTReverseRegisters (trace.state offset) frame input output)
    (hmetadata : TTReverseMetadata (trace.state offset).memory
      ((trace.state offset).natural 68+4*(trace.state offset).natural 84) m q (suffixSize (n::ns)) stride)
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (Z : Tensor ((q*n)::ns)) (hZ : StoresTensor (trace.state offset).memory input ((q*n)::ns) Z)
    (hQblock : DisjointBlocks frame (m*stride) output (m*suffixSize (n::ns)))
    (hZblock : DisjointBlocks input (q*suffixSize (n::ns)) output (m*suffixSize (n::ns))) :
    let p := liftMultiplyData (trace.state offset).memory m q (n::ns) frame stride input output
    let metadataTime := ttReverseMetadataTime m q (suffixSize (n::ns)) stride
    let time := offset+metadataTime+22+matrixMultiplyReturnTime p+8
    TTReverseResult (trace.state offset) (trace.state time) m q (n::ns) stride frame input output Q
      ((merge q n ns).symm Z) ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+metadataTime+22+
      17*(m+q+suffixSize (n::ns)+1)^3+8 := by
  exact ttReverse_at ht offset m q (n::ns) stride frame input output hl hs hr hmetadata hq Q hQ
    ((merge q n ns).symm Z) ((storesTensor_unmerge_iff _ input q n ns Z).mp hZ) hQblock hZblock

#assert_trust kernel TTReverseRegisters
#assert_trust kernel ttReverse_at
#assert_trust kernel ttReverse_unmerge_at
#print axioms ttReverse_at
#print axioms ttReverse_unmerge_at
end NLA.Proofs.TR04
