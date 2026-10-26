import NLA.Proofs.TR04.MachineTTRecursiveExecution
import NLA.Proofs.TR04.MachineTTStoreCandidate
import NLA.Proofs.TR04.TTFullBudget

/-! One actual candidate: gather its fixed first frame, execute all actual
child replies and saved lifts, then copy the resulting tensor into its slot. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation TTMemoryLayout
open TensorFormat TensorFormat.TTStrict

theorem ttCandidate_complete_at {start s0 : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (S : Shape) (r : Ranks S) (A : NLA.Computation.TensorTrainApproximation.Tensor S)
    (hrank : ∀ j,1≤r j) (hi : TTInitialSVDData S r A s0)
    {R : TTFirstReply s0} {hr : 1≤s0.natural 80}
    (hctx : TTFirstContext R hr (ofShape S) (trace.state offset))
    {n : ℕ} {ns : List ℕ} (hshape : modeList S.mode=s0.natural 81::n::ns)
    (hcols : suffixSize (n::ns)=s0.natural 82)
    (hl : (trace.state offset).label=189) (hs : (trace.state offset).status=.running)
    (hj : (trace.state offset).natural 76<(trace.state offset).natural 75) :
    ∃ elapsed : ℕ,∃ j : Fin R.family.count,
    ∃ Z : TensorFormat.Tensor ((R.family.width*n)::ns),
      elapsed≤8000*(Size S r+1)^4 ∧ j.val=(trace.state offset).natural 76 ∧
      Completion ((R.family.width*n)::ns) (fun i => originalRanks S r (i+1))
        (merge R.family.width n ns (contract (R.family.frame j) (Original.input hshape A))) Z ∧
      (trace.state (offset+elapsed)).label=189 ∧
      (trace.state (offset+elapsed)).status=.running ∧
      TTFirstContext R hr (ofShape S) (trace.state (offset+elapsed)) ∧
      (trace.state (offset+elapsed)).natural 76=(trace.state offset).natural 76+1 ∧
      (∀ x,(trace.state (offset+elapsed)).memory ((ofShape S).candidate j.val+Offset S x)=
        Original.output hshape (completionOutput (R.family.frame j) Z) x) ∧
      (∀ i<(trace.state offset).natural 76,∀ k<DenseSize S,
        (trace.state (offset+elapsed)).memory ((ofShape S).candidate i+k)=
          (trace.state offset).memory ((ofShape S).candidate i+k)) ∧
      CostThrough ttProgram trace (offset+elapsed)≤CostThrough ttProgram trace offset+8000*(Size S r+1)^4 := by
  let L := ofShape S
  let s := trace.state offset
  let gatherTime := s0.natural 81*(11*s.natural 106+7)+24
  let gathered := offset+gatherTime
  obtain ⟨j,hjval,hwidth,hgTime,hgLabel,hgRunning,hQ,hgContext,hgPres,hfields,hgCost⟩ :=
    hctx.gather ht offset s rfl hl hs hj
  have hgData := ttFirstCandidate_stage hctx hgContext hfields (Original.input hshape A)
    hcols (hi.read_original hshape) j hwidth hQ
  have hwidthStep := hctx.original_width hi hcols
  have H := @ttCore_complete_at start trace ht S r A hrank ns gathered 0 (s0.natural 81) n
  simp only [Nat.zero_add] at H
  have hzeroRank : (fun j => originalRanks S r (0+j))=originalRanks S r := by
    funext j
    rw [Nat.zero_add]
  have hwidthShift : R.family.width=stepRank (s0.natural 81) (n::ns) (fun j => originalRanks S r (0+j)) := by
    rw [hzeroRank]
    exact hwidthStep
  rw [←hwidthShift] at H
  have hreach : Dimensions.Reachable (modeList S.mode) (originalRanks S r) 0
      (s0.natural 81::n::ns) := by
    rw [←hshape]
    exact Dimensions.Reachable.start
  have hgHeader : ∀ a,a<L.input → (trace.state gathered).memory a=InputMemory S r A a := by
    intro a ha
    have ha' : a<L.firstU := by unfold Layout.firstU;omega
    exact (hgContext.savedPrefix a ha').trans (congrFun hi.memory a)
  obtain ⟨ec,Z,hec,hcore,hcoreCost⟩ := H (R.family.frame j) (Original.input hshape A)
    hreach hgLabel hgRunning hgData hgHeader
  let copied := gathered+ec
  have hpres : TTStagePreserves L 0 s (trace.state copied) := ttStagePreserves_trans hgPres hcore.preserves
  have hcContext : TTFirstContext R hr L (trace.state copied) := hctx.of_stage hpres
  have hcLabel : (trace.state copied).label=349 := by
    rw [hcore.label]
    rfl
  have hcPointer : (trace.state copied).natural 123=ttCandidateStoreBase (trace.state copied) := by
    rw [hcore.candidatePointer rfl]
    unfold ttCandidateStoreBase
    rw [hcore.preserves.2 71 (by unfold TTLoopKept;decide),
      hcore.preserves.2 76 (by unfold TTLoopKept;decide),
      hcore.preserves.2 64 (by unfold TTLoopKept;decide)]
  have hcStored : StoresTensor (trace.state copied).memory ((trace.state copied).natural 89)
      (s0.natural 81::n::ns) (completionOutput (R.family.frame j) Z) := hcore.currentStored
  obtain ⟨heCopy,hfinalLabel,hfinalRunning,hfinalContext,hfinalIndex,hstored,hearlier,_,_,_,hcopyCost⟩ :=
    ttCandidate_store_context_at ht copied S r A hi L hcContext hshape
      (completionOutput (R.family.frame j) Z) hcLabel hcore.running hcore.workPair hcPointer hcStored
  let elapsed := gatherTime+ec+(6*DenseSize S+10)
  have htime : copied+(6*DenseSize S+10)=offset+elapsed := by dsimp [copied,gathered,elapsed];omega
  rw [htime] at hfinalLabel hfinalRunning hfinalContext hfinalIndex hstored hearlier hcopyCost
  have hjCopy : (trace.state copied).natural 76=s.natural 76 := hpres.2 76 (by unfold TTLoopKept;decide)
  have hdepth : ns.length≤Size S r := by
    have hlen := congrArg List.length hshape
    rw [length_modeList] at hlen
    simp only [List.length_cons] at hlen
    have hord := (shape_order_le_denseSize S).trans (shape_denseSize_le_size S r)
    omega
  have hsize := shape_denseSize_le_size S r
  have hgEnvelope : 24*(L.entries+1)^2≤24*(Size S r+1)^2 :=
    Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left (by change DenseSize S+1≤Size S r+1;omega) 2)
  have hbudget := ttFullBudget_candidate (Size S r) ns.length hdepth
  refine ⟨elapsed,j,Z,?_,hjval,hcore.childCompletion,hfinalLabel,hfinalRunning,hfinalContext,?_,?_,?_,?_⟩
  · change gatherTime≤24*(L.entries+1)^2 at hgTime
    dsimp [elapsed]
    omega
  · exact hfinalIndex.trans (congrArg (·+1) hjCopy)
  · intro x
    rw [hjCopy,←hjval] at hstored
    exact hstored x
  · intro i hi' k hk
    rw [hearlier i (by rw [hjCopy];exact hi') k hk]
    apply hpres.1
    apply Or.inr;apply Or.inr;apply Or.inr
    unfold Layout.candidate
    omega
  · change CostThrough ttProgram trace gathered≤CostThrough ttProgram trace offset+24*(L.entries+1)^2 at hgCost
    change CostThrough ttProgram trace copied≤CostThrough ttProgram trace gathered+
      (3000*ns.length*ttRecursiveUnit (Size S r)+2000*ttRecursiveUnit (Size S r)) at hcoreCost
    omega

#assert_trust kernel ttCandidate_complete_at
#print axioms ttCandidate_complete_at
end NLA.Proofs.TR04
