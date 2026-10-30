import NLA.Proofs.TR04.MachineTTRecursiveExecution

/-! A complete actual child call, including its nondeterministic SVD instruction,
returns the tensor certified by Completion at the saved parent continuation.
All response bases, including tied and zero singular directions, remain legal. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat
open NLA.Computation.TensorTrainApproximation (Shape Ranks Size InputMemory)

 theorem ttChild_complete_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace)
    (S : Shape) (r : Ranks S) (A0 : NLA.Computation.TensorTrainApproximation.Tensor S)
    (hr : ∀ j,1≤r j) (offset level m n : ℕ) (ns : List ℕ) (A : Tensor (m::n::ns))
    (hreach : Dimensions.Reachable (modeList S.mode) (originalRanks S r) level (m::n::ns))
    (hl : (trace.state offset).label=237) (hs : (trace.state offset).status=.running)
    (ha : TTAllocationRegisters (ofShape S) (trace.state offset))
    (hlevel : (trace.state offset).natural 84=level)
    (hrows : (trace.state offset).natural 85=m)
    (hwidth : (trace.state offset).natural 86=stepRank m (n::ns) (fun j => originalRanks S r (level+j)))
    (hcols : (trace.state offset).natural 87=suffixSize (n::ns))
    (hframe : (trace.state offset).natural 94=(ofShape S).frame level)
    (hpair : TTWorkPair (ofShape S) (trace.state offset))
    (hA : StoresTensor (trace.state offset).memory ((trace.state offset).natural 89) (m::n::ns) A)
    (hheader : ∀ a,a<(ofShape S).input → (trace.state offset).memory a=InputMemory S r A0 a) :
    ∃ elapsed : ℕ,∃ Y : Tensor (m::n::ns),
      elapsed≤3000*(ns.length+1)*ttRecursiveUnit (Size S r) ∧
      Completion (m::n::ns) (fun j => originalRanks S r (level+j)) A Y ∧
      (trace.state (offset+elapsed)).label=(if level=0 then 349 else 287) ∧
      (trace.state (offset+elapsed)).status=.running ∧
      (trace.state (offset+elapsed)).natural 84=level-1 ∧
      StoresTensor (trace.state (offset+elapsed)).memory ((trace.state (offset+elapsed)).natural 89) (m::n::ns) Y ∧
      TTWorkPair (ofShape S) (trace.state (offset+elapsed)) ∧
      TTStagePreserves (ofShape S) level (trace.state offset) (trace.state (offset+elapsed)) ∧
      TTAllocationRegisters (ofShape S) (trace.state (offset+elapsed)) ∧
      CostThrough ttProgram trace (offset+elapsed)≤CostThrough ttProgram trace offset+
        3000*(ns.length+1)*ttRecursiveUnit (Size S r) := by
  let rank := fun j => originalRanks S r (level+j)
  have hb := hreach.original_step_bounds S r hr
  have hlevelBound := hreach.original_level_lt S r hr
  have hsize := shape_denseSize_le_size S r
  obtain ⟨U,sigma,V,hvalid,hlabel,hrunning,hdata,hprotected,hsvdCost⟩ :=
    ttChild_svd_stage_at ht offset (ofShape S) level m (n::ns) rank A hl hs ha hlevel hlevelBound
      hrows hwidth hcols hframe hpair hA hb.rows_le hb.cols_le
  have hchildHeader : ∀ address,address<(ofShape S).input →
      (trace.state (offset+4)).memory address=InputMemory S r A0 address := by
    intro address had
    exact (ttStagePreserves_header hprotected address had).trans (hheader address had)
  obtain ⟨ec,Z,hec,hcore,hcoreCost⟩ := ttCore_complete_at ht S r A0 hr ns (offset+4) level m n
    (stepFrame (n::ns) rank U) A hreach hlabel hrunning hdata hchildHeader
  have hfull := hcore.prefixCompletion hvalid
  have hbudget := ttRecursive_prefix_budget (Size S r) ns.length ((m+suffixSize (n::ns)+1)^3+3)
    (ttRecursive_cube_two (Size S r) m (suffixSize (n::ns))
      (hb.rows_le.trans hsize) (hb.cols_le.trans hsize))
  have htime : offset+4+ec=offset+(4+ec) := by omega
  have hsteps : 4≤(m+suffixSize (n::ns)+1)^3+3 := by
    have hp : 0<(m+suffixSize (n::ns)+1)^3 := by positivity
    omega
  have hp := ttStagePreserves_trans hprotected hcore.preserves
  refine ⟨4+ec,stepOutput rank U Z,by omega,hfull,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [←htime];exact hcore.label
  · rw [←htime];exact hcore.running
  · rw [←htime];exact hcore.levelValue
  · rw [←htime];exact hcore.currentStored
  · rw [←htime];exact hcore.workPair
  · rw [←htime];exact hp
  · rw [←htime];exact hcore.allocation
  · rw [←htime];omega

#assert_trust kernel ttChild_complete_at
#print axioms ttChild_complete_at
end NLA.Proofs.TR04
