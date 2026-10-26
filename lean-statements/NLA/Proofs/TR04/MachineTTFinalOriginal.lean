import NLA.Proofs.TR04.MachineTTFinalCopy
import NLA.Proofs.TR04.MachineTTFinalBest
import NLA.Proofs.TR04.MachineSquaredErrorOriginal

/-! Literal original tensor cells survive candidate-store copying; the actual
selector error is exactly FrobeniusSq for every stored candidate. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation

/-- Either actual dense work buffer is separated from every candidate slot.
The separation follows from the concrete allocation, with no capacity premise. -/
theorem ttCandidate_store_disjoint (s : State ttProgram) (L : TTMemoryLayout.Layout)
    (hN : s.natural 64=L.entries) (hstore : s.natural 71=L.store)
    (hsource : s.natural 89=L.workA ∨ s.natural 89=L.workB) :
    DisjointBlocks (s.natural 89) (s.natural 64) (ttCandidateStoreBase s) (s.natural 64) := by
  apply TTMemoryLayout.disjoint_of_end_le
  unfold ttCandidateStoreBase
  rw [hN,hstore]
  rcases hsource with hsource | hsource
  · rw [hsource]
    unfold TTMemoryLayout.Layout.store TTMemoryLayout.Layout.workB
    omega
  · rw [hsource]
    unfold TTMemoryLayout.Layout.store
    omega

/-- Copying a candidate cannot alter any earlier allocation or header cell. -/
theorem ttCandidate_copy_before_store (memory : ℕ → ℝ) (source store entries j a : ℕ)
    (ha : a<store) :
    copiedMemory memory source (store+j*entries) entries a=memory a := by
  apply copiedMemory_outside
  omega

/-- The actual current dense output is stored with the original literal
Offset convention. No ordering or tensor evaluator is supplied by this lemma. -/
theorem ttCandidate_copy_original_cells (S : Shape) (memory : ℕ → ℝ)
    (source store j : ℕ) (B : Tensor S)
    (hB : ∀ x,memory (source+Offset S x)=B x) :
    ∀ x,copiedMemory memory source (store+j*DenseSize S) (DenseSize S)
      (store+j*DenseSize S+Offset S x)=B x := by
  intro x
  rw [ttCandidate_copy_cell memory source store (DenseSize S) j (Offset S x)
    (TensorFormat.original_offset_lt_denseSize S x)]
  exact hB x

/-- Actual347→189 stores the original tensor and retains every earlier stored
candidate cell, including when another candidate wins later. -/
theorem ttCandidate_copy_original_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (S : Shape) (r : Ranks S) (B : Tensor S)
    (hl : (trace.state offset).label=347) (hs : (trace.state offset).status=.running)
    (hz : (trace.state offset).natural 127=0) (hN : (trace.state offset).natural 64=DenseSize S)
    (hd : DisjointBlocks ((trace.state offset).natural 89) ((trace.state offset).natural 64)
      (ttCandidateStoreBase (trace.state offset)) ((trace.state offset).natural 64))
    (hB : ∀ x,(trace.state offset).memory ((trace.state offset).natural 89+Offset S x)=B x) :
    let s := trace.state offset
    let time := offset+(6*DenseSize S+12)
    (trace.state time).label=189 ∧ (trace.state time).status=.running ∧
      (trace.state time).natural 76=s.natural 76+1 ∧
      (∀ x,(trace.state time).memory (s.natural 71+s.natural 76*DenseSize S+Offset S x)=B x) ∧
      (∀ i<s.natural 76,∀ k<DenseSize S,
        (trace.state time).memory (s.natural 71+i*DenseSize S+k)=s.memory (s.natural 71+i*DenseSize S+k)) ∧
      (∀ a,a<s.natural 71 → (trace.state time).memory a=s.memory a) ∧
      (∀ j : Fin 128,TTCopyFinalKept j → (trace.state time).natural j=s.natural j) ∧
      CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+18*(Size S r+1) := by
  obtain ⟨hl',hs',hj,hm,hn,_,hc⟩ := ttCandidate_copy_at ht offset hl hs hz hd
  simp only [hN] at hl' hs' hj hm hn hc
  refine ⟨hl',hs',hj,?_,?_,?_,hn,?_⟩
  · intro x
    rw [hm]
    change copiedMemory (trace.state offset).memory ((trace.state offset).natural 89)
      ((trace.state offset).natural 71+(trace.state offset).natural 76*(trace.state offset).natural 64)
      (DenseSize S) _=B x
    rw [hN]
    exact ttCandidate_copy_original_cells S _ _ _ _ B hB x
  · intro i hi k hk
    rw [hm]
    unfold ttCandidateStoreBase
    rw [hN]
    exact ttCandidate_copy_earlier _ _ _ _ _ i k hi hk
  · intro a ha
    rw [hm]
    unfold ttCandidateStoreBase
    rw [hN]
    exact ttCandidate_copy_before_store _ _ _ _ _ a ha
  · have hsize := shape_denseSize_le_size S r
    omega

/-- Each real error computed by the actual selector is the original tensor
Frobenius error, simultaneously for every candidate represented in memory. -/
theorem ttBestData_error_original (s : State ttProgram) (S : Shape) (A : Tensor S)
    (C : ℕ → Tensor S) (hN : s.natural 64=DenseSize S)
    (hA : ∀ x,s.memory (s.natural 92+Offset S x)=A x)
    (hC : ∀ i<s.natural 75,∀ x,s.memory (s.natural 71+i*DenseSize S+Offset S x)=C i x)
    (i : ℕ) (hi : i<s.natural 75) :
    (ttBestData s).candidateError i=FrobeniusSq S A (C i) := by
  change squaredErrorSum s.memory (s.natural 92) (s.natural 71+i*s.natural 64) (s.natural 64)=_
  rw [hN]
  exact squaredErrorSum_eq_frobeniusSq S s.memory _ _ A (C i) hA (hC i hi)

/-- Actual final189 branch, full selector and literal371 halt choose an actual
minimum among all stored candidates. All candidate arrays remain unchanged. -/
theorem ttBest_halt_original_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (S : Shape) (r : Ranks S)
    (A : Tensor S) (C : ℕ → Tensor S)
    (hl : (trace.state offset).label=189) (hs : (trace.state offset).status=.running)
    (hz : (trace.state offset).natural 127=0)
    (hp : 0<(trace.state offset).natural 75)
    (hfull : (trace.state offset).natural 75≤(trace.state offset).natural 76)
    (hK : (trace.state offset).natural 75≤DenseSize S)
    (hN : (trace.state offset).natural 64=DenseSize S)
    (hA : ∀ x,(trace.state offset).memory ((trace.state offset).natural 92+Offset S x)=A x)
    (hC : ∀ i<(trace.state offset).natural 75,∀ x,
      (trace.state offset).memory ((trace.state offset).natural 71+i*DenseSize S+Offset S x)=C i x) :
    let s := trace.state offset
    let time := offset+(bestCandidateReturnTime (ttBestData s)+17)
    ∃ winner<s.natural 75,
      (trace.state time).status=.halted (s.natural 71+winner*DenseSize S) ∧
      (trace.state time).natural 83=s.natural 71+winner*DenseSize S ∧
      (trace.state time).natural 54=winner ∧
      (trace.state time).real 12=FrobeniusSq S A (C winner) ∧
      (∀ i<s.natural 75,FrobeniusSq S A (C winner)≤FrobeniusSq S A (C i)) ∧
      (trace.state time).memory=s.memory ∧
      (∀ x,(trace.state time).memory (s.natural 71+winner*DenseSize S+Offset S x)=C winner x) ∧
      CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+300*(Size S r+1)^2 := by
  obtain ⟨winner,hw,hstatus,hbase,hwinner,herr,hmin,hm,_,_,hc⟩ := ttBest_halt_minimum_at ht offset hl hs hz hp hfull
  have he := ttBestData_error_original (trace.state offset) S A C hN hA hC
  simp only [hN] at hstatus hbase
  refine ⟨winner,hw,hstatus,hbase,hwinner,herr.trans (he winner hw),?_,hm,?_,?_⟩
  · intro i hi
    rw [← he winner hw,← he i hi]
    exact hmin i hi
  · intro x
    rw [hm]
    exact hC winner hw x
  · have hsize := shape_denseSize_le_size S r
    have hpoly : 67*((trace.state offset).natural 75+(trace.state offset).natural 64+1)^2≤300*(Size S r+1)^2 := by
      rw [hN]
      nlinarith [sq_nonneg ((Size S r : ℤ)+1),sq_nonneg ((DenseSize S : ℤ)+1)]
    exact hc.trans (Nat.add_le_add_left hpoly _)

#assert_trust kernel ttCandidate_store_disjoint
#assert_trust kernel ttCandidate_copy_before_store
#assert_trust kernel ttCandidate_copy_original_cells
#assert_trust kernel ttCandidate_copy_original_at
#assert_trust kernel ttBestData_error_original
#assert_trust kernel ttBest_halt_original_at
#print axioms ttCandidate_copy_original_at
#print axioms ttBest_halt_original_at
end NLA.Proofs.TR04
