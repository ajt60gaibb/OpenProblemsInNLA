import NLA.Proofs.TR04.TTMemoryLayoutMatrix
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace TTMemoryLayoutAuthorConsumer
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
open NLA.Proofs.TR04.TTMemoryLayout
 theorem literal_first_output_blocks (d N m l : ℕ) (hm : m ≤ N) (hl : l ≤ N) :
    OutputBlocksDisjoint m l (2*d-1+N) (2*d-1+N+N^2) (2*d-1+N+N^2+N) :=
  Layout.first_outputs_disjoint ⟨d,N⟩ m l hm hl
 theorem literal_child_output_blocks (d N level m l : ℕ) (hm : m ≤ N) (hl : l ≤ N) :
    OutputBlocksDisjoint m l
      (2*d-1+N+N^2+N+N^2+N+N^2+level*N^2)
      (2*d-1+N+N^2+N+N^2) (2*d-1+N+N^2+N+N^2+N) :=
  Layout.child_outputs_disjoint ⟨d,N⟩ level m l hm hl
 theorem literal_original_heap_bound (S : Shape) (r : Ranks S) (K : ℕ)
    (hK : K ≤ DenseSize S + 1) :
    2*S.order-1+DenseSize S+(DenseSize S)^2+DenseSize S+(DenseSize S)^2+
      DenseSize S+(DenseSize S)^2+S.order*(DenseSize S)^2+4*S.order+
      DenseSize S+DenseSize S+K*DenseSize S ≤20*(Size S r+1)^3 :=
  ofShape_endAddress_le_size S r K hK
 theorem literal_work_buffers (L : Layout) (m l a b : ℕ)
    (hml : m*l ≤ L.entries) (hab : a*b ≤ L.entries) :
    DisjointBlocks L.workA (m*l) L.workB (a*b) :=
  L.work_rectangle_disjoint m l a b hml hab
 theorem literal_transpose_contract_safety (L : Layout) (level m q cols : ℕ)
    (memory : ℕ → ℝ) (hlevel : level < L.order)
    (hm : m ≤ L.entries) (hq : q ≤ L.entries)
    (hmcols : m*cols ≤ L.entries) (hqcols : q*cols ≤ L.entries) :
    (L.contraction level m q cols memory).InputsOutsideOutput :=
  L.contraction_inputsOutsideOutput level m q cols memory hlevel hm hq hmcols hqcols
 theorem literal_empty_svd_outputs (L : Layout) :
    OutputBlocksDisjoint 0 0 L.firstU L.firstSigma L.firstV :=
  L.first_outputs_disjoint 0 0 (Nat.zero_le _) (Nat.zero_le _)
#assert_trust kernel literal_first_output_blocks
#assert_trust kernel literal_child_output_blocks
#assert_trust kernel literal_original_heap_bound
#assert_trust kernel literal_work_buffers
#assert_trust kernel literal_transpose_contract_safety
#assert_trust kernel literal_empty_svd_outputs
#print axioms literal_first_output_blocks
#print axioms literal_child_output_blocks
#print axioms literal_original_heap_bound
#print axioms literal_work_buffers
#print axioms literal_transpose_contract_safety
#print axioms literal_empty_svd_outputs
end TTMemoryLayoutAuthorConsumer
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.ofShape
#print axioms NLA.Proofs.TR04.TTMemoryLayout.ofShape
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.input
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.input
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.firstU
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.firstU
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.firstSigma
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.firstSigma
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.firstV
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.firstV
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.childSigma
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.childSigma
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.childV
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.childV
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frames
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frames
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frame
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frame
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.metadata
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.metadata
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.workA
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.workA
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.workB
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.workB
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.store
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.store
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.candidate
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.candidate
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Fits
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Fits
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.fits_same
#print axioms NLA.Proofs.TR04.TTMemoryLayout.fits_same
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.fits_trans
#print axioms NLA.Proofs.TR04.TTMemoryLayout.fits_trans
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.disjoint_symm
#print axioms NLA.Proofs.TR04.TTMemoryLayout.disjoint_symm
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.disjoint_of_end_le
#print axioms NLA.Proofs.TR04.TTMemoryLayout.disjoint_of_end_le
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.disjoint_fits
#print axioms NLA.Proofs.TR04.TTMemoryLayout.disjoint_fits
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.fits_address
#print axioms NLA.Proofs.TR04.TTMemoryLayout.fits_address
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.square_capacity
#print axioms NLA.Proofs.TR04.TTMemoryLayout.square_capacity
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.rectangle_capacity
#print axioms NLA.Proofs.TR04.TTMemoryLayout.rectangle_capacity
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_fits
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_fits
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_before_metadata
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_before_metadata
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frames_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frames_disjoint
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell_mem
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell_mem
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell_injective
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.metadataCell_injective
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.candidate_fits
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.candidate_fits
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.candidates_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.candidates_disjoint
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.first_outputs_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.first_outputs_disjoint
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.child_outputs_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.child_outputs_disjoint
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.header_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.header_disjoint
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.input_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.input_disjoint
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.firstU_before_workA
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.firstU_before_workA
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.firstV_before_workA
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.firstV_before_workA
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.firstSigma_before_workA
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.firstSigma_before_workA
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.input_before_workA
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.input_before_workA
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.childSigma_before_workA
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.childSigma_before_workA
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.childV_before_workA
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.childV_before_workA
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_before_workA
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_before_workA
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.before_work_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.before_work_disjoint
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.work_buffers_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.work_buffers_disjoint
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.workA_candidate_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.workA_candidate_disjoint
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.workB_candidate_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.workB_candidate_disjoint
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_metadata_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_metadata_disjoint
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_work_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_work_disjoint
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_rectangle_fits
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_rectangle_fits
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.workA_rectangle_fits
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.workA_rectangle_fits
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.workB_rectangle_fits
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.workB_rectangle_fits
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_workA_rectangle_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_workA_rectangle_disjoint
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.work_rectangle_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.work_rectangle_disjoint
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.writeSVD_preserves_disjoint_block
#print axioms NLA.Proofs.TR04.TTMemoryLayout.writeSVD_preserves_disjoint_block
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.write_firstSVD_prefix
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.write_firstSVD_prefix
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.write_childSVD_work
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.write_childSVD_work
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.firstU_frame_disjoint
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.firstU_frame_disjoint
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.write_firstSVD_later
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.write_firstSVD_later
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.write_childSVD_other_frame
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.write_childSVD_other_frame
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress_eq
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress_eq
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.store_le_endAddress
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.store_le_endAddress
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.metadata_before_store
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.metadata_before_store
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.workA_before_store
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.workA_before_store
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.workB_before_store
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.workB_before_store
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.prefix_address_lt_end
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.prefix_address_lt_end
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_address_lt_end
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.frame_address_lt_end
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.metadata_address_lt_end
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.metadata_address_lt_end
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.candidate_address_lt_end
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.candidate_address_lt_end
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress_le_cubic
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.endAddress_le_cubic
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.ofShape_input
#print axioms NLA.Proofs.TR04.TTMemoryLayout.ofShape_input
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.ofShape_endAddress_le_size
#print axioms NLA.Proofs.TR04.TTMemoryLayout.ofShape_endAddress_le_size
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.ofShape_allocated_address_lt_size
#print axioms NLA.Proofs.TR04.TTMemoryLayout.ofShape_allocated_address_lt_size
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.StageMetadata
#print axioms NLA.Proofs.TR04.TTMemoryLayout.StageMetadata
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.value
#print axioms NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.value
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.Bounded
#print axioms NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.Bounded
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.value_le
#print axioms NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.value_le
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.frame_capacity
#print axioms NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.frame_capacity
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.original_value_le_size
#print axioms NLA.Proofs.TR04.TTMemoryLayout.StageMetadata.original_value_le_size
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction_inputsOutsideOutput
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction_inputsOutsideOutput
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting_inputsOutsideOutput
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting_inputsOutsideOutput
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction_leftMatrix
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction_leftMatrix
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction_rightMatrix
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.contraction_rightMatrix
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting_leftMatrix
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting_leftMatrix
#assert_trust kernel NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting_rightMatrix
#print axioms NLA.Proofs.TR04.TTMemoryLayout.Layout.lifting_rightMatrix
