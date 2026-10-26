import NLA.Proofs.TR04.MachineTTRecursiveChild
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace RecursiveExecutionAuthorLiteralConsumer
open NLA.Computation.SVDMachine NLA.Proofs.TR04 NLA.Proofs.TR04.TensorFormat
open NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.TensorTrainApproximation (Shape Ranks Size InputMemory)

theorem literal_actual_shared_stage {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace)
    (S : Shape) (r : Ranks S) (A0 : NLA.Computation.TensorTrainApproximation.Tensor S)
    (hr : ∀ j,1≤r j) (ns : List ℕ) (offset level m n : ℕ)
    (Q : Matrix (Fin m) (Fin (stepRank m (n::ns) (fun j => originalRanks S r (level+j)))) ℝ)
    (A : Tensor (m::n::ns))
    (hreach : Dimensions.Reachable (modeList S.mode) (originalRanks S r) level (m::n::ns))
    (hl : (trace.state offset).label=241) (hs : (trace.state offset).status=.running)
    (ha : TTAllocationRegisters (ofShape S) (trace.state offset))
    (hlev : (trace.state offset).natural 84=level)
    (hrows : (trace.state offset).natural 85=m)
    (hwidth : (trace.state offset).natural 86=stepRank m (n::ns) (fun j => originalRanks S r (level+j)))
    (hcols : (trace.state offset).natural 87=suffixSize (n::ns))
    (hframe : (trace.state offset).natural 94=(ofShape S).frame level)
    (hstride : (trace.state offset).natural 88=stepRank m (n::ns) (fun j => originalRanks S r (level+j)) ∨
      (trace.state offset).natural 88=m)
    (hQ : StoresFrame (trace.state offset).memory ((ofShape S).frame level) ((trace.state offset).natural 88) Q)
    (hA : StoresTensor (trace.state offset).memory ((trace.state offset).natural 89) (m::n::ns) A)
    (hbuffers : ((trace.state offset).natural 108=0 ∧ (trace.state offset).natural 89=(ofShape S).input ∧
        (trace.state offset).natural 90=(ofShape S).workA) ∨
      ((trace.state offset).natural 108=1 ∧
        (((trace.state offset).natural 89=(ofShape S).workA ∧ (trace.state offset).natural 90=(ofShape S).workB) ∨
         ((trace.state offset).natural 89=(ofShape S).workB ∧ (trace.state offset).natural 90=(ofShape S).workA))))
    (hheader : ∀ a,a<(ofShape S).input → (trace.state offset).memory a=InputMemory S r A0 a) :
    ∃ elapsed : ℕ,∃ Z : Tensor ((stepRank m (n::ns) (fun j => originalRanks S r (level+j))*n)::ns),
      elapsed≤3000*ns.length*(Size S r+1)^3+2000*(Size S r+1)^3 ∧
      Completion ((stepRank m (n::ns) (fun j => originalRanks S r (level+j))*n)::ns)
        (fun j => originalRanks S r (level+(j+1)))
        (merge (stepRank m (n::ns) (fun j => originalRanks S r (level+j))) n ns (contract Q A)) Z ∧
      (trace.state (offset+elapsed)).label=(if level=0 then 349 else 287) ∧
      (trace.state (offset+elapsed)).status=.running ∧
      (trace.state (offset+elapsed)).natural 84=level-1 ∧
      StoresTensor (trace.state (offset+elapsed)).memory ((trace.state (offset+elapsed)).natural 89)
        (m::n::ns) (lift Q ((merge (stepRank m (n::ns) (fun j => originalRanks S r (level+j))) n ns).symm Z)) ∧
      TTWorkPair (ofShape S) (trace.state (offset+elapsed)) ∧
      (∀ address,TTStageProtected (ofShape S) level address →
        (trace.state (offset+elapsed)).memory address=(trace.state offset).memory address) ∧
      (∀ j : Fin 128,j ∈ ([0,64,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,92,
          103,104,105,106,125,126,127] : List (Fin 128)) →
        (trace.state (offset+elapsed)).natural j=(trace.state offset).natural j) ∧
      (level=0 → (trace.state (offset+elapsed)).natural 123=
        (trace.state offset).natural 71+(trace.state offset).natural 76*(trace.state offset).natural 64) ∧
      CostThrough ttProgram trace (offset+elapsed)≤CostThrough ttProgram trace offset+
        (3000*ns.length*(Size S r+1)^3+2000*(Size S r+1)^3) := by
  obtain ⟨elapsed,Z,he,h,hc⟩ := ttCore_complete_at ht S r A0 hr ns offset level m n Q A hreach hl hs
    ⟨ha,hlev,hrows,hwidth,hcols,hframe,hstride,hQ,hA,hbuffers⟩ hheader
  exact ⟨elapsed,Z,he,h.childCompletion,h.label,h.running,h.levelValue,h.currentStored,h.workPair,
    h.preserves.1,h.preserves.2,h.candidatePointer,hc⟩

theorem literal_actual_child_parent_return {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace)
    (S : Shape) (r : Ranks S) (A0 : NLA.Computation.TensorTrainApproximation.Tensor S)
    (hr : ∀ j,1≤r j) (offset level m n : ℕ) (ns : List ℕ) (A : Tensor (m::n::ns))
    (hreach : Dimensions.Reachable (modeList S.mode) (originalRanks S r) level (m::n::ns))
    (hpositive : 0<level)
    (hl : (trace.state offset).label=237) (hs : (trace.state offset).status=.running)
    (ha : TTAllocationRegisters (ofShape S) (trace.state offset))
    (hlev : (trace.state offset).natural 84=level)
    (hrows : (trace.state offset).natural 85=m)
    (hwidth : (trace.state offset).natural 86=stepRank m (n::ns) (fun j => originalRanks S r (level+j)))
    (hcols : (trace.state offset).natural 87=suffixSize (n::ns))
    (hframe : (trace.state offset).natural 94=(ofShape S).frame level)
    (hpair : TTWorkPair (ofShape S) (trace.state offset))
    (hA : StoresTensor (trace.state offset).memory ((trace.state offset).natural 89) (m::n::ns) A)
    (hheader : ∀ a,a<(ofShape S).input → (trace.state offset).memory a=InputMemory S r A0 a) :
    ∃ elapsed : ℕ,∃ Y : Tensor (m::n::ns),elapsed≤3000*(ns.length+1)*(Size S r+1)^3 ∧
      Completion (m::n::ns) (fun j => originalRanks S r (level+j)) A Y ∧
      (trace.state (offset+elapsed)).label=287 ∧ (trace.state (offset+elapsed)).status=.running ∧
      (trace.state (offset+elapsed)).natural 84+1=level ∧
      StoresTensor (trace.state (offset+elapsed)).memory ((trace.state (offset+elapsed)).natural 89) (m::n::ns) Y ∧
      TTWorkPair (ofShape S) (trace.state (offset+elapsed)) ∧
      TTStagePreserves (ofShape S) level (trace.state offset) (trace.state (offset+elapsed)) ∧
      CostThrough ttProgram trace (offset+elapsed)≤CostThrough ttProgram trace offset+
        3000*(ns.length+1)*(Size S r+1)^3 := by
  obtain ⟨elapsed,Y,he,hcomp,hlabel,hrun,hlevel,hstore,hwork,hprotect,_,hcost⟩ :=
    ttChild_complete_at ht S r A0 hr offset level m n ns A hreach hl hs ha hlev hrows hwidth hcols hframe hpair hA hheader
  refine ⟨elapsed,Y,he,hcomp,?_,hrun,by omega,hstore,hwork,hprotect,hcost⟩
  rw [hlabel,if_neg (by omega)]

#assert_trust kernel literal_actual_shared_stage
#assert_trust kernel literal_actual_child_parent_return
#print axioms literal_actual_shared_stage
#print axioms literal_actual_child_parent_return
end RecursiveExecutionAuthorLiteralConsumer
#assert_trust kernel NLA.Proofs.TR04.TTStageBuffers
#print axioms NLA.Proofs.TR04.TTStageBuffers
#assert_trust kernel NLA.Proofs.TR04.TTWorkPair.current_ge
#print axioms NLA.Proofs.TR04.TTWorkPair.current_ge
#assert_trust kernel NLA.Proofs.TR04.TTWorkPair.output_choice
#print axioms NLA.Proofs.TR04.TTWorkPair.output_choice
#assert_trust kernel NLA.Proofs.TR04.TTWorkPair.disjoint
#print axioms NLA.Proofs.TR04.TTWorkPair.disjoint
#assert_trust kernel NLA.Proofs.TR04.TTStageBuffers.output_choice
#print axioms NLA.Proofs.TR04.TTStageBuffers.output_choice
#assert_trust kernel NLA.Proofs.TR04.TTStageBuffers.input_output_disjoint
#print axioms NLA.Proofs.TR04.TTStageBuffers.input_output_disjoint
#assert_trust kernel NLA.Proofs.TR04.ttFrame_output_disjoint
#print axioms NLA.Proofs.TR04.ttFrame_output_disjoint
#assert_trust kernel NLA.Proofs.TR04.ttLoopKept_reverse
#print axioms NLA.Proofs.TR04.ttLoopKept_reverse
#assert_trust kernel NLA.Proofs.TR04.TTReverseResult.stagePreserves
#print axioms NLA.Proofs.TR04.TTReverseResult.stagePreserves
#assert_trust kernel NLA.Proofs.TR04.TTReverseResult.workPair
#print axioms NLA.Proofs.TR04.TTReverseResult.workPair
#assert_trust kernel NLA.Proofs.TR04.ttStagePreserves_header
#print axioms NLA.Proofs.TR04.ttStagePreserves_header
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.next_mode_header
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.next_mode_header
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.forward_test_iff
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.forward_test_iff
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.shifted_rank_succ
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.shifted_rank_succ
#assert_trust kernel NLA.Proofs.TR04.TTStageData
#print axioms NLA.Proofs.TR04.TTStageData
#assert_trust kernel NLA.Proofs.TR04.TTStageData.stride_bounds
#print axioms NLA.Proofs.TR04.TTStageData.stride_bounds
#assert_trust kernel NLA.Proofs.TR04.TTStageBuffers.input_choice
#print axioms NLA.Proofs.TR04.TTStageBuffers.input_choice
#assert_trust kernel NLA.Proofs.TR04.ttStage_input_metadata_disjoint
#print axioms NLA.Proofs.TR04.ttStage_input_metadata_disjoint
#assert_trust kernel NLA.Proofs.TR04.ttStage_frame_metadata_disjoint
#print axioms NLA.Proofs.TR04.ttStage_frame_metadata_disjoint
#assert_trust kernel NLA.Proofs.TR04.ttStage_metadata_at
#print axioms NLA.Proofs.TR04.ttStage_metadata_at
#assert_trust kernel NLA.Proofs.TR04.TTReverseMetadata.memory_eq
#print axioms NLA.Proofs.TR04.TTReverseMetadata.memory_eq
#assert_trust kernel NLA.Proofs.TR04.TTStageForwardResult
#print axioms NLA.Proofs.TR04.TTStageForwardResult
#assert_trust kernel NLA.Proofs.TR04.ttStageForward_pack
#print axioms NLA.Proofs.TR04.ttStageForward_pack
#assert_trust kernel NLA.Proofs.TR04.ttStage_forward_at
#print axioms NLA.Proofs.TR04.ttStage_forward_at
#assert_trust kernel NLA.Proofs.TR04.ttRecursiveUnit
#print axioms NLA.Proofs.TR04.ttRecursiveUnit
#assert_trust kernel NLA.Proofs.TR04.ttRecursiveUnit_pos
#print axioms NLA.Proofs.TR04.ttRecursiveUnit_pos
#assert_trust kernel NLA.Proofs.TR04.ttRecursiveUnit_linear
#print axioms NLA.Proofs.TR04.ttRecursiveUnit_linear
#assert_trust kernel NLA.Proofs.TR04.ttRecursive_cube_three
#print axioms NLA.Proofs.TR04.ttRecursive_cube_three
#assert_trust kernel NLA.Proofs.TR04.ttRecursive_cube_two
#print axioms NLA.Proofs.TR04.ttRecursive_cube_two
#assert_trust kernel NLA.Proofs.TR04.ttRecursive_own_stage_budget
#print axioms NLA.Proofs.TR04.ttRecursive_own_stage_budget
#assert_trust kernel NLA.Proofs.TR04.ttRecursive_prefix_budget
#print axioms NLA.Proofs.TR04.ttRecursive_prefix_budget
#assert_trust kernel NLA.Proofs.TR04.ttChild_svd_stage_at
#print axioms NLA.Proofs.TR04.ttChild_svd_stage_at
#assert_trust kernel NLA.Proofs.TR04.TTCoreResult
#print axioms NLA.Proofs.TR04.TTCoreResult
#assert_trust kernel NLA.Proofs.TR04.TTCoreResult.prefixCompletion
#print axioms NLA.Proofs.TR04.TTCoreResult.prefixCompletion
#assert_trust kernel NLA.Proofs.TR04.ttLoopKept_not_level
#print axioms NLA.Proofs.TR04.ttLoopKept_not_level
#assert_trust kernel NLA.Proofs.TR04.ttReverseStart_preserves
#print axioms NLA.Proofs.TR04.ttReverseStart_preserves
#assert_trust kernel NLA.Proofs.TR04.ttReverseStart_workPair
#print axioms NLA.Proofs.TR04.ttReverseStart_workPair
#assert_trust kernel NLA.Proofs.TR04.ttStage_reverse_at
#print axioms NLA.Proofs.TR04.ttStage_reverse_at
#assert_trust kernel NLA.Proofs.TR04.ttCore_two_at
#print axioms NLA.Proofs.TR04.ttCore_two_at
#assert_trust kernel NLA.Proofs.TR04.ttCore_complete_at
#print axioms NLA.Proofs.TR04.ttCore_complete_at
#assert_trust kernel NLA.Proofs.TR04.ttChild_complete_at
#print axioms NLA.Proofs.TR04.ttChild_complete_at
