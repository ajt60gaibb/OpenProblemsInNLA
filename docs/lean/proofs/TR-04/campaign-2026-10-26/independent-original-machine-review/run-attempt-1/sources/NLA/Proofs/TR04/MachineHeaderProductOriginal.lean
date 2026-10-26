import NLA.Proofs.TR04.ShapeInitializationBounds
import NLA.Proofs.TR04.MachineHeaderProduct

/-! The actual header-product run at the immutable TR-04 input boundary.
Every decoded header value comes from literal InputMemory. The returned
natural register and charged-time estimate use the actual dense tensor size. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation

theorem headerPrefixProduct_shape (S : Shape) :
    headerPrefixProduct (shapeHeaderValues S) S.order = DenseSize S :=
  shapeHeaderValues_product S

theorem headerPrefixProduct_shape_le (S : Shape) (i : ℕ) (hi : i ≤ S.order) :
    headerPrefixProduct (shapeHeaderValues S) i ≤ DenseSize S := by
  rw [← headerPrefixProduct_shape S]
  unfold headerPrefixProduct
  apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.range_mono hi)
  intro j hj _
  have hj' : j < S.order := Finset.mem_range.mp hj
  simp only [shapeHeaderValues, dif_pos hj']
  have := S.mode_ge ⟨j, hj'⟩
  omega

theorem headerPrefixTime_shape (S : Shape) :
    headerPrefixTime (shapeHeaderValues S) S.order = 3 * (∑ i, S.mode i) + 7 * S.order := by
  calc
    headerPrefixTime (shapeHeaderValues S) S.order =
        3 * (∑ j ∈ Finset.range S.order, shapeHeaderValues S j) + S.order * 7 := by
      simp [headerPrefixTime, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 3 * (∑ i, S.mode i) + 7 * S.order := by
      rw [shapeHeaderValues_sum, Nat.mul_comm S.order 7]

theorem headerProductTime_shape (S : Shape) :
    headerProductTime (shapeHeaderValues S) S.order =
      3 * (∑ i, S.mode i) + 7 * S.order + 4 := by
  rw [headerProductTime, headerPrefixTime_shape]

theorem headerProductTime_shape_le_size (S : Shape) (r : Ranks S) :
    headerProductTime (shapeHeaderValues S) S.order ≤ 7 * Size S r := by
  rw [headerProductTime_shape]
  have hs := shape_sum_modes_le_denseSize S
  unfold Size
  omega

/-- The literal original start has actual legal traces for the fixed finite
header-product program; trace correctness is not made vacuous by an oracle. -/
theorem shape_headerProduct_trace_exists (S : Shape) (r : Ranks S) (A : Tensor S) :
    ∃ trace : Trace headerProductProgram,
      LegalTrace headerProductProgram (Start headerProductProgram S r A) trace :=
  exists_legalTrace _ _

/-- Every legal trace from the literal original Start computes the real dense
size in natural register2, preserves the entire input memory, and obeys the
uniform linear charged-cost bound. -/
theorem shape_headerProduct_trace_result (S : Shape) (r : Ranks S) (A : Tensor S)
    (trace : Trace headerProductProgram)
    (ht : LegalTrace headerProductProgram (Start headerProductProgram S r A) trace) :
    (trace.state (headerProductTime (shapeHeaderValues S) S.order)).natural 2 = DenseSize S ∧
    (trace.state (headerProductTime (shapeHeaderValues S) S.order)).status = .halted (DenseSize S) ∧
    (trace.state (headerProductTime (shapeHeaderValues S) S.order)).memory = InputMemory S r A ∧
    CostThrough headerProductProgram trace (headerProductTime (shapeHeaderValues S) S.order) ≤
      7 * Size S r := by
  obtain ⟨counter, registers, hr⟩ := headerProduct_trace_result (InputMemory S r A) S.order
    (shapeHeaderValues S) (inputMemory_shapeHeader S r A) trace ht
  have hc := headerProduct_trace_cost (InputMemory S r A) S.order (shapeHeaderValues S) trace ht
  refine ⟨?_, ?_, ?_, hc.trans (headerProductTime_shape_le_size S r)⟩
  · rw [hr]
    change headerPrefixProduct (shapeHeaderValues S) S.order = DenseSize S
    exact headerPrefixProduct_shape S
  · rw [hr]
    change Status.halted (headerPrefixProduct (shapeHeaderValues S) S.order) = .halted (DenseSize S)
    rw [headerPrefixProduct_shape]
  · rw [hr]
    rfl

#assert_trust kernel headerPrefixProduct_shape
#assert_trust kernel headerPrefixTime_shape
#assert_trust kernel headerProductTime_shape
#assert_trust kernel headerProductTime_shape_le_size
#assert_trust kernel shape_headerProduct_trace_exists
#assert_trust kernel shape_headerProduct_trace_result
#print axioms headerProductTime_shape_le_size
#print axioms shape_headerProduct_trace_result
end NLA.Proofs.TR04
