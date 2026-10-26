import NLA.Proofs.TR04.MachineTTCandidateExecution
import NLA.Proofs.TR04.MachineTTCompletedCandidates
import NLA.Proofs.TR04.MachineTTCandidateLoopInduction

/-! Execute every frame of the one fixed first family. The induction records
actual child completions and the literal original output in each stored slot. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation TTMemoryLayout
open TensorFormat TensorFormat.TTStrict

theorem ttCandidates_all_at {start s0 : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (S : Shape) (r : Ranks S) (A : NLA.Computation.TensorTrainApproximation.Tensor S)
    (hrank : ∀ j,1≤r j) (hi : TTInitialSVDData S r A s0)
    {R : TTFirstReply s0} {hr : 1≤s0.natural 80}
    (hctx : TTFirstContext R hr (ofShape S) (trace.state offset))
    {n : ℕ} {ns : List ℕ} (hshape : modeList S.mode=s0.natural 81::n::ns)
    (hcols : suffixSize (n::ns)=s0.natural 82)
    (hl : (trace.state offset).label=189) (hs : (trace.state offset).status=.running)
    (hj : (trace.state offset).natural 76=0) :
    ∃ elapsed : ℕ,elapsed≤R.family.count*(8000*(Size S r+1)^4) ∧
      (trace.state (offset+elapsed)).label=189 ∧
      (trace.state (offset+elapsed)).status=.running ∧
      TTFirstContext R hr (ofShape S) (trace.state (offset+elapsed)) ∧
      (trace.state (offset+elapsed)).natural 76=R.family.count ∧
      TTCompletedCandidates S r A hshape R.family (trace.state (offset+elapsed)) R.family.count ∧
      CostThrough ttProgram trace (offset+elapsed)≤CostThrough ttProgram trace offset+
        R.family.count*(8000*(Size S r+1)^4) := by
  let L := ofShape S
  let budget := 8000*(Size S r+1)^4
  let I := fun s : State ttProgram => TTFirstContext R hr L s ∧
    TTCompletedCandidates S r A hshape R.family s (s.natural 76)
  have initial : I (trace.state offset) := by
    refine ⟨hctx,?_⟩
    rw [hj]
    exact ttCompletedCandidates_zero S r A hshape R.family _
  have advance : ∀ off : ℕ,I (trace.state off) →
      (trace.state off).label=189 → (trace.state off).status=.running →
      (trace.state off).natural 76<R.family.count →
      ∃ elapsed : ℕ,elapsed≤budget ∧ I (trace.state (off+elapsed)) ∧
        (trace.state (off+elapsed)).label=189 ∧ (trace.state (off+elapsed)).status=.running ∧
        (trace.state (off+elapsed)).natural 76=(trace.state off).natural 76+1 ∧
        CostThrough ttProgram trace (off+elapsed)≤CostThrough ttProgram trace off+budget := by
    intro off hold hlabel hrunning hindex
    obtain ⟨oldContext,oldCompleted⟩ := hold
    have hindex' : (trace.state off).natural 76<(trace.state off).natural 75 := by
      rw [oldContext.count_eq]
      exact hindex
    obtain ⟨e,j,Z,he,hjval,hZ,hl',hs',hc',hj',hstored,hearlier,hcost⟩ :=
      ttCandidate_complete_at ht off S r A hrank hi oldContext hshape hcols hlabel hrunning hindex'
    have hn71 : (trace.state (off+e)).natural 71=(trace.state off).natural 71 :=
      hc'.allocation.store.trans oldContext.allocation.store.symm
    have hdone : TTCompletedCandidates S r A hshape R.family (trace.state off) j.val := by
      rw [hjval]
      exact oldCompleted
    have hmem : ∀ i<j.val,∀ x,
        (trace.state (off+e)).memory ((trace.state off).natural 71+i*DenseSize S+Offset S x)=
          (trace.state off).memory ((trace.state off).natural 71+i*DenseSize S+Offset S x) := by
      intro i hi' x
      rw [oldContext.allocation.store]
      exact hearlier i (by rwa [←hjval]) (Offset S x) (original_offset_lt_denseSize S x)
    have hnew : ∀ x,(trace.state (off+e)).memory
        ((trace.state off).natural 71+j.val*DenseSize S+Offset S x)=
          Original.output hshape (completionOutput (R.family.frame j) Z) x := by
      intro x
      rw [oldContext.allocation.store]
      exact hstored x
    have hcompleted := hdone.extend j hn71 hmem Z hZ hnew
    have hcompleted' : TTCompletedCandidates S r A hshape R.family
        (trace.state (off+e)) ((trace.state (off+e)).natural 76) := by
      rw [hj',←hjval]
      exact hcompleted
    exact ⟨e,he,⟨hc',hcompleted'⟩,hl',hs',hj',hcost⟩
  obtain ⟨e,he,hfinal,hl',hs',hj',hcost⟩ :=
    ttCandidateLoop_induction trace R.family.count budget I advance offset initial hl hs hj
  refine ⟨e,he,hl',hs',hfinal.1,hj',?_,hcost⟩
  have hh := hfinal.2
  rwa [hj'] at hh

#assert_trust kernel ttCandidates_all_at
#print axioms ttCandidates_all_at
end NLA.Proofs.TR04
