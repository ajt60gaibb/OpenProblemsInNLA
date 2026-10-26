import NLA.Proofs.TR04.MachineSquaredErrorTrace
import NLA.Proofs.TR04.TensorCompressionRadixDecode
import NLA.Proofs.TR04.ShapeInitializationBounds

/-! The actual dense squared-error loop computes the original tensor
Frobenius error. Representation hypotheses describe literal memory cells;
the mixed-radix bijection proves complete, collision-free enumeration. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation

theorem originalRadixIndexEquiv_eq_decode (S : Shape) (i : Fin (DenseSize S)) :
    TensorFormat.originalRadixIndexEquiv S i = Decode S i.val := by
  apply TensorFormat.original_offset_injective S
  rw [TensorFormat.originalRadixIndexEquiv_offset,
    TensorFormat.original_offset_decode S i.val i.isLt]

theorem tensor_memory_cells_iff (S : Shape) (memory : ℕ → ℝ) (base : ℕ) (A : Tensor S) :
    (∀ x, memory (base + Offset S x) = A x) ↔
      (∀ i < DenseSize S, memory (base + i) = A (Decode S i)) := by
  constructor
  · intro h i hi
    have hh := h (Decode S i)
    rwa [TensorFormat.original_offset_decode S i hi] at hh
  · intro h x
    have hh := h (Offset S x) (TensorFormat.original_offset_lt_denseSize S x)
    simpa only [TensorFormat.original_decode_offset] using hh

theorem squaredErrorSum_eq_frobeniusSq (S : Shape) (memory : ℕ → ℝ)
    (baseA baseB : ℕ) (A B : Tensor S)
    (hA : ∀ x, memory (baseA + Offset S x) = A x)
    (hB : ∀ x, memory (baseB + Offset S x) = B x) :
    squaredErrorSum memory baseA baseB (DenseSize S) = FrobeniusSq S A B := by
  unfold squaredErrorSum FrobeniusSq
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ i : Fin (DenseSize S), (memory (baseA + i.val) - memory (baseB + i.val))^2) =
        ∑ i : Fin (DenseSize S),
          (A (TensorFormat.originalRadixIndexEquiv S i) -
            B (TensorFormat.originalRadixIndexEquiv S i))^2 := by
      apply Finset.sum_congr rfl
      intro i _
      have ha := hA (TensorFormat.originalRadixIndexEquiv S i)
      have hb := hB (TensorFormat.originalRadixIndexEquiv S i)
      rw [TensorFormat.originalRadixIndexEquiv_offset] at ha hb
      rw [ha, hb]
    _ = ∑ x : Index S, (A x - B x)^2 :=
      (TensorFormat.originalRadixIndexEquiv S).sum_comp (fun x => (A x - B x)^2)

theorem squaredErrorTime_shape_le_size (S : Shape) (r : Ranks S) :
    9 * DenseSize S + 2 ≤ 11 * Size S r := by
  unfold Size
  omega

/-- An arbitrary actual caller obtains the literal original Frobenius error
at its continuation, with unchanged memory and preserved outside-frame
registers. The arrays may overlap; no optimizer or error oracle is supplied. -/
theorem RoutineEmbedding.squaredError_run_frobenius {Q : Program}
    (E : RoutineEmbedding squaredErrorProgram Q) (S : Shape) (r : Ranks S)
    (memory : ℕ → ℝ) (baseA baseB : ℕ) (A B : Tensor S)
    (hA : ∀ x, memory (baseA + Offset S x) = A x)
    (hB : ∀ x, memory (baseB + Offset S x) = B x)
    (accumulator scratchA scratchB : ℝ) {start : State Q} {trace : Trace Q} (offset : ℕ)
    (hs : E.Relates (squaredErrorStart memory baseA baseB (DenseSize S)
      accumulator scratchA scratchB) (trace.state offset)) (ht : LegalTrace Q start trace) :
    (trace.state (offset + (9 * DenseSize S + 2))).label = E.labels 10 ∧
    (trace.state (offset + (9 * DenseSize S + 2))).real (E.reals 0) = FrobeniusSq S A B ∧
    (trace.state (offset + (9 * DenseSize S + 2))).memory = memory ∧
    (trace.state (offset + (9 * DenseSize S + 2))).status = .running ∧
    CostThrough Q trace (offset + (9 * DenseSize S + 2)) ≤
      CostThrough Q trace offset + (9 * DenseSize S + 2) ∧
    CostThrough Q trace (offset + (9 * DenseSize S + 2)) ≤
      CostThrough Q trace offset + 11 * Size S r ∧
    (∀ j : Fin Q.realRegisters, (∀ i, j ≠ E.reals i) →
      (trace.state (offset + (9 * DenseSize S + 2))).real j = (trace.state offset).real j) ∧
    (∀ j : Fin (Q.extraNatRegisters + 1), (∀ i, j ≠ E.naturals i) →
      (trace.state (offset + (9 * DenseSize S + 2))).natural j =
        (trace.state offset).natural j) := by
  obtain ⟨hl, hv, hm, hr, hc⟩ := E.squaredError_run_value memory baseA baseB (DenseSize S)
    accumulator scratchA scratchB offset hs ht
  rw [squaredErrorSum_eq_frobeniusSq S memory baseA baseB A B hA hB] at hv
  have hno := squaredErrorProgram_nohalt_prefix memory baseA baseB (DenseSize S)
    accumulator scratchA scratchB
  have hscalar : ∀ k < 9 * DenseSize S + 2,
      instructionIsSVD (squaredErrorProgram.code ((ordinaryStep squaredErrorProgram)^[k]
        (squaredErrorStart memory baseA baseB (DenseSize S) accumulator scratchA scratchB)).label) =
        false := fun _ _ => squaredErrorProgram_scalar _
  refine ⟨hl, hv, hm, hr, hc, ?_, ?_, ?_⟩
  · exact hc.trans (Nat.add_le_add_left (squaredErrorTime_shape_le_size S r) _)
  · intro j hj
    exact E.scalar_trace_real_outside _ hs (legalTrace_shift ht offset) _ hno hscalar j hj
  · intro j hj
    exact E.scalar_trace_natural_outside _ hs (legalTrace_shift ht offset) _ hno hscalar j hj

#assert_trust kernel originalRadixIndexEquiv_eq_decode
#assert_trust kernel tensor_memory_cells_iff
#assert_trust kernel squaredErrorSum_eq_frobeniusSq
#assert_trust kernel squaredErrorTime_shape_le_size
#assert_trust kernel RoutineEmbedding.squaredError_run_frobenius
#print axioms squaredErrorSum_eq_frobeniusSq
#print axioms RoutineEmbedding.squaredError_run_frobenius
end NLA.Proofs.TR04
