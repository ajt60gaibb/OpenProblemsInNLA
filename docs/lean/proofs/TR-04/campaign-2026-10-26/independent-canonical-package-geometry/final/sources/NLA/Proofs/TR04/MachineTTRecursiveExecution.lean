import NLA.Proofs.TR04.MachineTTRecursiveBase
import NLA.Proofs.TR04.MachineTTChildInitializationOriginal
import NLA.Proofs.TR04.TTRecursiveDimensions

/-! Actual finite controller recursion. Reachability of the literal original
shape derives all capacities and decreases the remaining list. Every child
SVD is read from the supplied legal trace. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
open NLA.Computation.TensorTrainApproximation (Shape Ranks DenseSize Size InputMemory)

 theorem ttCore_complete_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace)
    (S : Shape) (r : Ranks S) (A0 : NLA.Computation.TensorTrainApproximation.Tensor S)
    (hr : ∀ j,1≤r j) (ns : List ℕ) (offset level m n : ℕ)
    (Q : Matrix (Fin m) (Fin (stepRank m (n::ns) (fun j => originalRanks S r (level+j)))) ℝ)
    (A : Tensor (m::n::ns))
    (hreach : Dimensions.Reachable (modeList S.mode) (originalRanks S r) level (m::n::ns))
    (hl : (trace.state offset).label=241) (hs : (trace.state offset).status=.running)
    (hd : TTStageData (ofShape S) level m (stepRank m (n::ns) (fun j => originalRanks S r (level+j)))
      (n::ns) Q A (trace.state offset))
    (hheader : ∀ a,a<(ofShape S).input → (trace.state offset).memory a=InputMemory S r A0 a) :
    ∃ elapsed : ℕ,∃ Z : Tensor ((stepRank m (n::ns) (fun j => originalRanks S r (level+j))*n)::ns),
      elapsed≤3000*ns.length*ttRecursiveUnit (Size S r)+2000*ttRecursiveUnit (Size S r) ∧
      TTCoreResult (trace.state offset) (trace.state (offset+elapsed)) (ofShape S) level m
        (stepRank m (n::ns) (fun j => originalRanks S r (level+j))) n ns
        (fun j => originalRanks S r (level+j)) Q A Z ∧
      CostThrough ttProgram trace (offset+elapsed)≤CostThrough ttProgram trace offset+
        (3000*ns.length*ttRecursiveUnit (Size S r)+2000*ttRecursiveUnit (Size S r)) := by
  induction ns generalizing offset level m n with
  | nil =>
    have hb := hreach.original_step_bounds S r hr
    have hlen := (hreach.original_invariants S r hr).2.2.2
    simp only [List.length_cons,List.length_nil] at hlen
    obtain ⟨elapsed,Z,he,hresult,hcost⟩ := ttCore_two_at ht offset (ofShape S) (Size S r) level m
      (stepRank m [n] (fun j => originalRanks S r (level+j))) n (fun j => originalRanks S r (level+j))
      Q A hl hs hd (by change level+2=S.order;omega) (Dimensions.stepRank_le_rows _ _ _)
      hb.rows_le hb.input_dense_le hb.cols_le (shape_denseSize_le_size S r)
    exact ⟨elapsed,Z,by simpa using he,hresult,by simpa using hcost⟩
  | cons a ns ih =>
    let L := ofShape S
    let rank := fun j => originalRanks S r (level+j)
    let q := stepRank m (n::a::ns) rank
    let childRank := fun j => originalRanks S r ((level+1)+j)
    let X : Tensor ((q*n)::a::ns) := merge q n (a::ns) (contract Q A)
    have hb := hreach.original_step_bounds S r hr
    have hlevel : level<L.order := hreach.original_level_lt S r hr
    have hqm : q≤m := Dimensions.stepRank_le_rows _ _ _
    have hsize : L.entries≤Size S r := shape_denseSize_le_size S r
    obtain ⟨ef,hef,hf,hfCost⟩ := ttStage_forward_at ht offset L level m q n (a::ns) Q A hl hs hd
      hlevel hqm hb.rows_le hb.input_dense_le
    have hfLabel : (trace.state (offset+ef)).label=208 := by
      rw [hf.label]
      exact if_pos ((hreach.forward_test_iff S r hr).mpr (by simp))
    have hcReach : Dimensions.Reachable (modeList S.mode) (originalRanks S r) (level+1) ((q*n)::a::ns) :=
      Dimensions.Reachable.step hreach
    have hfHeader : ∀ address,address<L.input →
        (trace.state (offset+ef)).memory address=InputMemory S r A0 address := by
      intro address had
      exact (ttStagePreserves_header hf.preserves address had).trans (hheader address had)
    have hfRows : (trace.state (offset+ef)).natural 100*shapeHeaderValues S (level+1)=q*n := by
      rw [hf.previousRank,hreach.next_mode_header S r hr]
    obtain ⟨ec,hec,hi,hiAllocation,hiRows,hiCols,hiWidth,hiFrame,hbChild,hiCost⟩ :=
      ttChild_initialize_original_at ht (offset+ef) S r A0 hr (level+1) (q*n) a ns hcReach
        hfLabel hf.running hf.allocation hf.levelValue hfRows hfHeader
    let svdTime := offset+ef+ec
    have hiLevel : (trace.state svdTime).natural 84=level+1 :=
      (hi.preserves.2 84 (by unfold TTChildKept;decide)).trans hf.levelValue
    have hiPair : TTWorkPair L (trace.state svdTime) := by
      rcases hf.workPair with ⟨hin,hout⟩|⟨hin,hout⟩
      · exact Or.inl ⟨(hi.preserves.2 89 (by unfold TTChildKept;decide)).trans hin,
          (hi.preserves.2 90 (by unfold TTChildKept;decide)).trans hout⟩
      · exact Or.inr ⟨(hi.preserves.2 89 (by unfold TTChildKept;decide)).trans hin,
          (hi.preserves.2 90 (by unfold TTChildKept;decide)).trans hout⟩
    have hiX : StoresTensor (trace.state svdTime).memory ((trace.state svdTime).natural 89) ((q*n)::a::ns) X := by
      rw [hi.preserves.1,hi.preserves.2 89 (by unfold TTChildKept;decide)]
      exact hf.currentStored
    have hcLevel : level+1<L.order := hcReach.original_level_lt S r hr
    obtain ⟨U,sigma,V,hvalid,hchildLabel,hchildRunning,hchildData,hsvdPreserves,hsvdCost⟩ :=
      ttChild_svd_stage_at ht svdTime L (level+1) (q*n) (a::ns) childRank X hi.label hi.running
        hiAllocation hiLevel hcLevel hiRows hiWidth hiCols hiFrame hiPair hiX hbChild.rows_le hbChild.cols_le
    let childTime := svdTime+4
    have htoChild : TTStagePreserves L (level+1) (trace.state (offset+ef)) (trace.state childTime) :=
      ttStagePreserves_trans (ttChildPreserves_stage hi.preserves) hsvdPreserves
    have hchildHeader : ∀ address,address<L.input →
        (trace.state childTime).memory address=InputMemory S r A0 address := by
      intro address had
      exact (ttStagePreserves_header htoChild address had).trans (hfHeader address had)
    obtain ⟨ei,Z,hei,hcore,hcoreCost⟩ := ih childTime (level+1) (q*n) a
      (stepFrame (a::ns) childRank U) X hcReach hchildLabel hchildRunning hchildData hchildHeader
    let readTime := childTime+ei
    let Y : Tensor ((q*n)::a::ns) := stepOutput childRank U Z
    have hcompletion : Completion ((q*n)::a::ns) (fun j => rank (j+1)) X Y := by
      have hfull := hcore.prefixCompletion hvalid
      simpa only [rank,childRank,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hfull
    have hreadLabel : (trace.state readTime).label=287 := by
      rw [hcore.label,if_neg (by omega)]
    have hreadLevel : (trace.state readTime).natural 84=level := by rw [hcore.levelValue];omega
    have hY : StoresTensor (trace.state readTime).memory ((trace.state readTime).natural 89) ((q*n)::a::ns) Y :=
      hcore.currentStored
    have hprotected : TTStagePreserves L (level+1) (trace.state (offset+ef)) (trace.state readTime) :=
      ttStagePreserves_trans htoChild hcore.preserves
    obtain ⟨er,her,hresult,hreverseCost⟩ := ttStage_reverse_at ht (trace.state offset) (offset+ef) readTime
      L level m q n (a::ns) rank Q A Y hd hf hprotected hreadLabel hcore.running hreadLevel
      hcore.workPair hY hcompletion hlevel hqm hb.rows_le hb.input_dense_le
    rw [ttReverseMetadataTime_eq] at her hreverseCost
    have hstride := (hd.stride_bounds hqm hb.rows_le).2.trans hsize
    have hown := ttRecursive_own_stage_budget (Size S r) m q (suffixSize (n::a::ns))
      ((trace.state offset).natural 88) (hb.rows_le.trans hsize) (hb.rank_le.trans hsize)
      (hb.cols_le.trans hsize) hstride
    have hSVD := ttRecursive_cube_two (Size S r) (q*n) (suffixSize (a::ns))
      (hbChild.rows_le.trans hsize) (hbChild.cols_le.trans hsize)
    have hprefix := ttRecursive_prefix_budget (Size S r) ns.length
      ((q*n+suffixSize (a::ns)+1)^3+3) hSVD
    let elapsed := ef+ec+4+ei+er
    have htime : readTime+er=offset+elapsed := by dsimp [readTime,childTime,svdTime,elapsed];omega
    rw [htime] at hresult hreverseCost
    refine ⟨elapsed,Y,?_,hresult,?_⟩
    · dsimp [elapsed]
      omega
    · dsimp [readTime,childTime,svdTime] at hreverseCost hcoreCost hsvdCost
      simp only [List.length_cons]
      omega

#assert_trust kernel ttCore_complete_at
#print axioms ttCore_complete_at
end NLA.Proofs.TR04
