import NLA.Proofs.TR04.TTDimensionBoundsReachable
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace TTDimensionAuthorConsumer
open NLA.Computation.TensorTrainApproximation
open NLA.Proofs.TR04.TensorFormat NLA.Proofs.TR04.TensorFormat.Dimensions
 theorem literal_all_natural_product_reduction (m n : ℕ) (ns : List ℕ) (r : ℕ → ℕ) :
    (min (r 0) (min m (Fintype.card (Index (n::ns)))) * n) * ns.prod ≤
      m * (n * ns.prod) := step_prod_le m n ns r
 theorem literal_reachable_work_and_squares (S : Shape) (r : Ranks S)
    (hr : ∀ j, 1 ≤ r j) (level m n : ℕ) (ns : List ℕ)
    (h : Reachable (modeList S.mode) (originalRanks S r) level (m::n::ns)) :
    let q := stepRank m (n::ns) (fun j => originalRanks S r (level+j))
    let cols := Fintype.card (Index (n::ns))
    0<m ∧ 0<q ∧ 0<cols ∧ 0<q*n ∧
      m≤DenseSize S ∧ q≤DenseSize S ∧ cols≤DenseSize S ∧
      m*cols≤DenseSize S ∧ q*cols≤DenseSize S ∧
      (q*n)*ns.prod≤DenseSize S ∧
      m*m≤(DenseSize S)^2 ∧ m*q≤(DenseSize S)^2 ∧ cols*cols≤(DenseSize S)^2 := by
  have hb := h.original_step_bounds S r hr
  exact ⟨hb.rows_pos,hb.rank_pos,hb.cols_pos,hb.child_mode_pos,hb.rows_le,hb.rank_le,
    hb.cols_le,hb.input_dense_le,hb.contracted_dense_le,hb.child_prod_le,
    hb.frame_square_le,hb.frame_rectangle_le,hb.right_square_le⟩
 theorem literal_suffix_layout (S : Shape) (r : Ranks S) (level m n : ℕ) (ns : List ℕ)
    (h : Reachable (modeList S.mode) (originalRanks S r) level (m::n::ns)) :
    Fintype.card (Index (n::ns)) = ((modeList S.mode).drop (level+1)).prod :=
  h.original_suffix S r
 theorem literal_two_modes_terminate (m n : ℕ) (r : ℕ → ℕ) :
    ((stepRank m [n] r * n)::([]:List ℕ)).length = 1 := rfl
 theorem literal_zero_request (m : ℕ) (ns : List ℕ) :
    stepRank m ns (fun _ => 0) = 0 := by simp [stepRank,cappedRank]
#assert_trust kernel literal_all_natural_product_reduction
#assert_trust kernel literal_reachable_work_and_squares
#assert_trust kernel literal_suffix_layout
#assert_trust kernel literal_two_modes_terminate
#assert_trust kernel literal_zero_request
#print axioms literal_all_natural_product_reduction
#print axioms literal_reachable_work_and_squares
#print axioms literal_suffix_layout
#print axioms literal_two_modes_terminate
#print axioms literal_zero_request
end TTDimensionAuthorConsumer
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.PositiveModes
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.PositiveModes
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.PositiveRanks
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.PositiveRanks
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_cons
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_cons
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_prod
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_prod
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.suffixSize_eq_prod
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.suffixSize_eq_prod
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.suffixSize_pos
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.suffixSize_pos
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.mode_le_prod
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.mode_le_prod
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_rows
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_rows
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_cols
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_cols
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_request
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_le_request
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_pos
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.stepRank_pos
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.step_prod_le
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.step_prod_le
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.step_compressed_dense_le
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.step_compressed_dense_le
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.step_length
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.step_length
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.step_positiveModes
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.step_positiveModes
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.step_positiveRanks
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.step_positiveRanks
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.StepBounds
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.StepBounds
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.step_bounds_of_product
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.step_bounds_of_product
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.invariants
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.invariants
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.step_bounds
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.step_bounds
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.nonempty
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.nonempty
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.tail_drop
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.tail_drop
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.tail_eq_drop
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.tail_eq_drop
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.level_lt
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.level_lt
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_original
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.positiveModes_original
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.positiveRanks_original
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.positiveRanks_original
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_invariants
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_invariants
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_step_bounds
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_step_bounds
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_level_lt
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_level_lt
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_suffix
#print axioms NLA.Proofs.TR04.TensorFormat.Dimensions.Reachable.original_suffix
