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
