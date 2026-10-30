import NLA.Proofs.TR04.MachineTTFirstOriginal
import NLA.Proofs.TR04.MachineTTFinalCopy349

/-! Exact original output storage at the actual reverse349 continuation. Saved
first-response data survives the copy and the actual candidate index advances;
all capacities and memory separation follow from the original allocation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation TTMemoryLayout
open TensorFormat TensorFormat.TTStrict

/-- Literal reverse direction of the stored original tensor representation. -/
theorem ttStoresTensor_original_output (S : Shape) {ms : List ℕ}
    (hl : modeList S.mode=ms) (memory : ℕ → ℝ) (base : ℕ) (X : TensorFormat.Tensor ms)
    (hX : StoresTensor memory base ms X) :
    ∀ x,memory (base+Offset S x)=Original.output hl X x := by
  subst ms
  intro x
  change memory (base+Offset S x)=X ((vectorIndexEquiv S.mode).symm x)
  have hh := hX ((vectorIndexEquiv S.mode).symm x)
  rwa [original_radixOffset] at hh

/-- Copy's scratch registers exclude every fixed first-family global; only
its actual candidate index is deliberately permitted to change. -/
theorem ttLoopKept_copyFinal (j : Fin 128) (hj : TTLoopKept j) (h76 : j≠76) :
    TTCopyFinalKept j := by
  simp only [TTLoopKept,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact False.elim (h76 rfl) | unfold TTCopyFinalKept;decide

/-- The concrete child-sigma boundary lies before every candidate slot. -/
theorem tt_childSigma_le_store (L : Layout) : L.childSigma≤L.store := by
  have hh := L.childSigma_before_workA
  unfold Layout.store Layout.workB
  omega

/-- Actual349 output storage preserves the fixed first response and frame
family for the next candidate. No mathematical completion is manufactured:
X is precisely the full original-format tensor already stored by the trace. -/
theorem ttCandidate_store_context_at {start s0 : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (S : Shape) (r : Ranks S) (A : NLA.Computation.TensorTrainApproximation.Tensor S)
    (hi : TTInitialSVDData S r A s0) {R : TTFirstReply s0} {hr : 1≤s0.natural 80}
    (L : Layout) (hctx : TTFirstContext R hr L (trace.state offset))
    {ms : List ℕ} (hshape : modeList S.mode=ms) (X : TensorFormat.Tensor ms)
    (hl : (trace.state offset).label=349) (hs : (trace.state offset).status=.running)
    (hpair : TTWorkPair L (trace.state offset))
    (hptr : (trace.state offset).natural 123=ttCandidateStoreBase (trace.state offset))
    (hX : StoresTensor (trace.state offset).memory ((trace.state offset).natural 89) ms X) :
    let s := trace.state offset
    let elapsed := 6*DenseSize S+10
    let time := offset+elapsed
    elapsed≤18*(Size S r+1) ∧
      (trace.state time).label=189 ∧ (trace.state time).status=.running ∧
      TTFirstContext R hr L (trace.state time) ∧
      (trace.state time).natural 76=s.natural 76+1 ∧
      (∀ x,(trace.state time).memory (L.candidate (s.natural 76)+Offset S x)=Original.output hshape X x) ∧
      (∀ i<s.natural 76,∀ k<DenseSize S,
        (trace.state time).memory (L.candidate i+k)=s.memory (L.candidate i+k)) ∧
      (∀ a,a<L.childSigma → (trace.state time).memory a=s.memory a) ∧
      TTWorkPair L (trace.state time) ∧
      (∀ j : Fin 128,TTCopyFinalKept j → (trace.state time).natural j=s.natural j) ∧
      CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+18*(Size S r+1) := by
  let s := trace.state offset
  have hentries : L.entries=DenseSize S := by
    rw [←hctx.input_count,hi.rows,hi.cols]
    exact ttFirstCols_prod S
  have hN : s.natural 64=DenseSize S := hctx.allocation.entries.trans hentries
  have hsource : s.natural 89=L.workA ∨ s.natural 89=L.workB := hpair.imp And.left And.left
  have hd := ttCandidate_store_disjoint s L hctx.allocation.entries hctx.allocation.store hsource
  have hB : ∀ x,s.memory (s.natural 89+Offset S x)=Original.output hshape X x :=
    ttStoresTensor_original_output S hshape s.memory (s.natural 89) X hX
  obtain ⟨hlabel,hrunning,hindex,hstored,hearlier,hprefix,hnatural,hcost⟩ :=
    ttCandidate_copy349_original_at ht offset S r (Original.output hshape X) hl hs hctx.allocation.zero hptr hN hd hB
  let time := offset+(6*DenseSize S+10)
  have hlow : ∀ a,a<L.childSigma → (trace.state time).memory a=s.memory a := by
    intro a ha
    apply hprefix a
    rw [hctx.allocation.store]
    exact ha.trans_le (tt_childSigma_le_store L)
  have hcontext : TTFirstContext R hr L (trace.state time) :=
    hctx.transfer hlow (fun j hj h76 => hnatural j (ttLoopKept_copyFinal j hj h76))
  have hnewpair : TTWorkPair L (trace.state time) := by
    have h89 := hnatural 89 (by unfold TTCopyFinalKept;decide)
    have h90 := hnatural 90 (by unfold TTCopyFinalKept;decide)
    rcases hpair with hpair | hpair
    · exact Or.inl ⟨h89.trans hpair.1,h90.trans hpair.2⟩
    · exact Or.inr ⟨h89.trans hpair.1,h90.trans hpair.2⟩
  refine ⟨?_,hlabel,hrunning,hcontext,hindex,?_,?_,hlow,hnewpair,hnatural,hcost⟩
  · have hb := shape_denseSize_le_size S r
    omega
  · intro x
    change (trace.state time).memory (L.store+s.natural 76*L.entries+Offset S x)=_
    rw [hentries,←hctx.allocation.store]
    exact hstored x
  · intro i hi' k hk
    change (trace.state time).memory (L.store+i*L.entries+k)=s.memory (L.store+i*L.entries+k)
    rw [hentries,←hctx.allocation.store]
    exact hearlier i hi' k hk

#assert_trust kernel ttStoresTensor_original_output
#assert_trust kernel ttLoopKept_copyFinal
#assert_trust kernel tt_childSigma_le_store
#assert_trust kernel ttCandidate_store_context_at
#print axioms ttCandidate_store_context_at
end NLA.Proofs.TR04
