import NLA.Proofs.TR04.MachineTTForwardCall

/-! Actual forward contraction through its caller continuation. The first
return selects the two allocated work buffers. Later returns swap only the
current and next work buffers. All input and metadata preservation below is
proved from actual memory separation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat

def TTForwardStable (i : Fin 128) : Prop :=
  ((i.val < 4) ∨ (21 ≤ i.val)) ∧ i≠97 ∧ TTForwardReturnStable i

structure TTForwardResult (old final : State ttProgram)
    (m q : ℕ) (ns : List ℕ) (stride frame input output next : ℕ)
    (Q : Matrix (Fin m) (Fin q) ℝ) (A : Tensor (m::ns)) : Prop where
  label : final.label=(if old.natural 84+1<old.natural 0-1 then 208 else 286)
  running : final.status=.running
  current : final.natural 89=output
  nextBuffer : final.natural 90=next
  previousRank : final.natural 100=q
  level : final.natural 84=old.natural 84+1
  lastLevel : final.natural 110=old.natural 0-1
  outputStored : StoresTensor final.memory output (q::ns) (contract Q A)
  inputStored : StoresTensor final.memory input (m::ns) A
  frameStored : StoresFrame final.memory frame stride Q
  memoryOutside : ∀ a, ¬(output≤a ∧ a<output+q*suffixSize ns) → final.memory a=old.memory a
  realOutside : ∀ i : Fin 16, ((i.val < 2) ∨ (5 ≤ i.val)) → final.real i=old.real i
  naturalOutside : ∀ i : Fin 128, TTForwardStable i → final.natural i=old.natural i

 theorem TTForwardResult.currentStored {old final : State ttProgram}
    {m q : ℕ} {ns : List ℕ} {stride frame input output next : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (m::ns)}
    (h : TTForwardResult old final m q ns stride frame input output next Q A) :
    StoresTensor final.memory (final.natural 89) (q::ns) (contract Q A) := by
  rw [h.current]
  exact h.outputStored

 theorem TTForwardResult.metadata {old final : State ttProgram}
    {m q : ℕ} {ns : List ℕ} {stride frame input output next : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (m::ns)}
    (h : TTForwardResult old final m q ns stride frame input output next Q A)
    (base count : ℕ) (hd : DisjointBlocks base count output (q*suffixSize ns)) :
    ∀ a, base≤a ∧ a<base+count → final.memory a=old.memory a := by
  intro a ha
  exact h.memoryOutside a (disjointBlocks_not_mem_right hd ha)

 theorem TTForwardResult.mergedStored {old final : State ttProgram}
    {m q n : ℕ} {ns : List ℕ} {stride frame input output next : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (m::n::ns)}
    (h : TTForwardResult old final m q (n::ns) stride frame input output next Q A) :
    StoresTensor final.memory (final.natural 89) ((q*n)::ns)
      (merge q n ns (contract Q A)) := by
  exact (storesTensor_merge_iff _ _ q n ns _).mp h.currentStored

 theorem ttForward_first_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (m q : ℕ) (ns : List ℕ) (stride frame input output : ℕ)
    (hl : (trace.state offset).label=255) (hs : (trace.state offset).status=.running)
    (hr : TTForwardRegisters (trace.state offset) m q (suffixSize ns) stride frame input output 0)
    (hw : (trace.state offset).natural 69=output)
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (A : Tensor (m::ns)) (hA : StoresTensor (trace.state offset).memory input (m::ns) A)
    (hQblock : DisjointBlocks frame (m*stride) output (q*suffixSize ns))
    (hAblock : DisjointBlocks input (m*suffixSize ns) output (q*suffixSize ns)) :
    let p := contractMultiplyData (trace.state offset).memory m q ns frame stride input output
    let time := offset+19+matrixMultiplyReturnTime p+9
    TTForwardResult (trace.state offset) (trace.state time) m q ns stride frame input output
      ((trace.state offset).natural 70) Q A ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+19+17*(q+m+suffixSize ns+1)^3+9 := by
  let s := trace.state offset
  let p := contractMultiplyData s.memory m q ns frame stride input output
  let time := offset+19+matrixMultiplyReturnTime p
  obtain ⟨hp,hstatus,hout,hin,hframe,hmem,hcost,hreal,hnatural,htag⟩ :=
    ttForward_contract_at ht offset m q ns stride frame input output 0 hl hs hr hq Q hQ A hA hQblock hAblock
  have hn (i : Fin 128) (hi : (i.val < 4) ∨ (21 ≤ i.val)) (hi97 : i≠97) :
      (trace.state time).natural i=s.natural i := hnatural i hi hi97
  have hz : (trace.state time).natural 127=0 := (hn 127 (by decide) (by decide)).trans hr.zero
  obtain ⟨he,hc⟩ := ttForwardFirst_return_at ht time hp hstatus htag hz
  obtain ⟨hlabel,hcurrent,hnext,hrank,hlevel,hlast,hMemory,hReal⟩ :=
    ttForwardFirstEnd_fields (trace.state time)
  refine ⟨?_,hc.trans (Nat.add_le_add_right hcost 9)⟩
  rw [he]
  constructor
  · rw [hlabel,hn 84 (by decide) (by decide),hn 0 (by decide) (by decide)]
  · rfl
  · exact hcurrent.trans ((hn 69 (by decide) (by decide)).trans hw)
  · exact hnext.trans (hn 70 (by decide) (by decide))
  · exact hrank.trans ((hn 86 (by decide) (by decide)).trans hr.width)
  · rw [hlevel,hn 84 (by decide) (by decide)]
  · rw [hlast,hn 0 (by decide) (by decide)]
  · rw [hMemory];exact hout
  · rw [hMemory];exact hin
  · rw [hMemory];exact hframe
  · rw [hMemory];exact hmem
  · rw [hReal];exact hreal
  · intro i hi
    exact (ttForwardFirstEnd_natural _ i hi.2.2).trans (hn i hi.1 hi.2.1)

 theorem ttForward_child_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (m q : ℕ) (ns : List ℕ) (stride frame input output : ℕ)
    (hl : (trace.state offset).label=255) (hs : (trace.state offset).status=.running)
    (hr : TTForwardRegisters (trace.state offset) m q (suffixSize ns) stride frame input output 1)
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (A : Tensor (m::ns)) (hA : StoresTensor (trace.state offset).memory input (m::ns) A)
    (hQblock : DisjointBlocks frame (m*stride) output (q*suffixSize ns))
    (hAblock : DisjointBlocks input (m*suffixSize ns) output (q*suffixSize ns)) :
    let p := contractMultiplyData (trace.state offset).memory m q ns frame stride input output
    let time := offset+19+matrixMultiplyReturnTime p+11
    TTForwardResult (trace.state offset) (trace.state time) m q ns stride frame input output input Q A ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+19+17*(q+m+suffixSize ns+1)^3+11 := by
  let s := trace.state offset
  let p := contractMultiplyData s.memory m q ns frame stride input output
  let time := offset+19+matrixMultiplyReturnTime p
  obtain ⟨hp,hstatus,hout,hin,hframe,hmem,hcost,hreal,hnatural,htag⟩ :=
    ttForward_contract_at ht offset m q ns stride frame input output 1 hl hs hr hq Q hQ A hA hQblock hAblock
  have hn (i : Fin 128) (hi : (i.val < 4) ∨ (21 ≤ i.val)) (hi97 : i≠97) :
      (trace.state time).natural i=s.natural i := hnatural i hi hi97
  have hz : (trace.state time).natural 127=0 := (hn 127 (by decide) (by decide)).trans hr.zero
  have ho : (trace.state time).natural 126=1 := (hn 126 (by decide) (by decide)).trans hr.one
  obtain ⟨he,hc⟩ := ttForwardChild_return_at ht time hp hstatus htag hz ho
  obtain ⟨hlabel,hcurrent,hnext,hrank,hlevel,hlast,hMemory,hReal⟩ :=
    ttForwardChildEnd_fields (trace.state time)
  refine ⟨?_,hc.trans (Nat.add_le_add_right hcost 11)⟩
  rw [he]
  constructor
  · rw [hlabel,hn 84 (by decide) (by decide),hn 0 (by decide) (by decide)]
  · rfl
  · exact hcurrent.trans ((hn 90 (by decide) (by decide)).trans hr.outputBase)
  · exact hnext.trans ((hn 89 (by decide) (by decide)).trans hr.inputBase)
  · exact hrank.trans ((hn 86 (by decide) (by decide)).trans hr.width)
  · rw [hlevel,hn 84 (by decide) (by decide)]
  · rw [hlast,hn 0 (by decide) (by decide)]
  · rw [hMemory];exact hout
  · rw [hMemory];exact hin
  · rw [hMemory];exact hframe
  · rw [hMemory];exact hmem
  · rw [hReal];exact hreal
  · intro i hi
    exact (ttForwardChildEnd_natural _ i hi.2.2).trans (hn i hi.1 hi.2.1)

#assert_trust kernel TTForwardResult
#assert_trust kernel TTForwardResult.currentStored
#assert_trust kernel TTForwardResult.metadata
#assert_trust kernel TTForwardResult.mergedStored
#assert_trust kernel ttForward_first_at
#assert_trust kernel ttForward_child_at
#print axioms ttForward_first_at
#print axioms ttForward_child_at
end NLA.Proofs.TR04
