import NLA.Proofs.TR04.MachineHeaderProductOriginal
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators
namespace ShapeHeaderOriginalConsumer
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation NLA.Proofs.TR04
 theorem actual_shape_bounds (S : Shape) :
    0 < (∏ i, S.mode i) ∧ (∑ i, S.mode i) ≤ (∏ i, S.mode i) ∧
    S.order ≤ (∏ i, S.mode i) ∧
    (∀ i, S.mode i ≤ (∏ j, S.mode j)) ∧
    (∀ i, SuffixSize S i ≤ (∏ j, S.mode j)) :=
  ⟨shape_denseSize_pos S, shape_sum_modes_le_denseSize S, shape_order_le_denseSize S,
    shape_mode_le_denseSize S, shape_suffix_le_denseSize S⟩
 theorem actual_literal_start (S : Shape) (r : Ranks S) (A : Tensor S)
    (trace : Trace headerProductProgram)
    (ht : LegalTrace headerProductProgram
      (initial headerProductProgram S.order (InputMemory S r A)) trace) :
    ∃ time : ℕ,
      time = 3 * (∑ i, S.mode i) + 7 * S.order + 4 ∧
      time ≤ 7 * ((∏ i, S.mode i) + S.order + (∑ j, r j) + 1) ∧
      (trace.state time).natural 2 = (∏ i, S.mode i) ∧
      (trace.state time).status = .halted (∏ i, S.mode i) ∧
      (trace.state time).memory = InputMemory S r A ∧
      CostThrough headerProductProgram trace time ≤
        7 * ((∏ i, S.mode i) + S.order + (∑ j, r j) + 1) := by
  obtain ⟨hn, hs, hm, hc⟩ := shape_headerProduct_trace_result S r A trace ht
  exact ⟨headerProductTime (shapeHeaderValues S) S.order, headerProductTime_shape S,
    headerProductTime_shape_le_size S r, hn, hs, hm, hc⟩
#assert_trust kernel actual_shape_bounds
#assert_trust kernel actual_literal_start
#print axioms actual_shape_bounds
#print axioms actual_literal_start
end ShapeHeaderOriginalConsumer
#assert_trust kernel NLA.Proofs.TR04.shapeHeaderValues
#print axioms NLA.Proofs.TR04.shapeHeaderValues
#assert_trust kernel NLA.Proofs.TR04.shapeHeaderValues_fin
#print axioms NLA.Proofs.TR04.shapeHeaderValues_fin
#assert_trust kernel NLA.Proofs.TR04.inputMemory_shapeHeader
#print axioms NLA.Proofs.TR04.inputMemory_shapeHeader
#assert_trust kernel NLA.Proofs.TR04.shapeHeaderValues_sum
#print axioms NLA.Proofs.TR04.shapeHeaderValues_sum
#assert_trust kernel NLA.Proofs.TR04.shapeHeaderValues_product
#print axioms NLA.Proofs.TR04.shapeHeaderValues_product
#assert_trust kernel NLA.Proofs.TR04.fin_sum_le_prod_of_two_le_aux
#print axioms NLA.Proofs.TR04.fin_sum_le_prod_of_two_le_aux
#assert_trust kernel NLA.Proofs.TR04.fin_sum_le_prod_of_two_le
#print axioms NLA.Proofs.TR04.fin_sum_le_prod_of_two_le
#assert_trust kernel NLA.Proofs.TR04.shape_sum_modes_le_denseSize
#print axioms NLA.Proofs.TR04.shape_sum_modes_le_denseSize
#assert_trust kernel NLA.Proofs.TR04.shape_denseSize_pos
#print axioms NLA.Proofs.TR04.shape_denseSize_pos
#assert_trust kernel NLA.Proofs.TR04.shape_order_le_denseSize
#print axioms NLA.Proofs.TR04.shape_order_le_denseSize
#assert_trust kernel NLA.Proofs.TR04.shape_mode_le_denseSize
#print axioms NLA.Proofs.TR04.shape_mode_le_denseSize
#assert_trust kernel NLA.Proofs.TR04.shape_suffix_pos
#print axioms NLA.Proofs.TR04.shape_suffix_pos
#assert_trust kernel NLA.Proofs.TR04.shape_suffix_le_denseSize
#print axioms NLA.Proofs.TR04.shape_suffix_le_denseSize
#assert_trust kernel NLA.Proofs.TR04.shape_denseSize_le_size
#print axioms NLA.Proofs.TR04.shape_denseSize_le_size
#assert_trust kernel NLA.Proofs.TR04.headerPrefixProduct_shape
#print axioms NLA.Proofs.TR04.headerPrefixProduct_shape
#assert_trust kernel NLA.Proofs.TR04.headerPrefixProduct_shape_le
#print axioms NLA.Proofs.TR04.headerPrefixProduct_shape_le
#assert_trust kernel NLA.Proofs.TR04.headerPrefixTime_shape
#print axioms NLA.Proofs.TR04.headerPrefixTime_shape
#assert_trust kernel NLA.Proofs.TR04.headerProductTime_shape
#print axioms NLA.Proofs.TR04.headerProductTime_shape
#assert_trust kernel NLA.Proofs.TR04.headerProductTime_shape_le_size
#print axioms NLA.Proofs.TR04.headerProductTime_shape_le_size
#assert_trust kernel NLA.Proofs.TR04.shape_headerProduct_trace_exists
#print axioms NLA.Proofs.TR04.shape_headerProduct_trace_exists
#assert_trust kernel NLA.Proofs.TR04.shape_headerProduct_trace_result
#print axioms NLA.Proofs.TR04.shape_headerProduct_trace_result
