import NLA.Proofs.TR04.MachineTensorMultiplyData

/-! Actual caller traces store the literal tensor contraction/lifting.
Both inputs remain stored, and all memory/registers outside the injected
routine/output frame retain their values. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR04
open TensorFormat
open NLA.Computation.SVDMachine

theorem RoutineEmbedding.contract_run_at {Caller : Program}
    (E : NLA.Proofs.TR04.RoutineEmbedding matrixMultiplyProgram Caller)
    {m q : ℕ} {ns : List ℕ} (memory : ℕ → ℝ)
    (frameBase stride inputBase outputBase : ℕ) (hq : q ≤ stride)
    (Q : Matrix (Fin m) (Fin q) ℝ) (hQ : StoresFrame memory frameBase stride Q)
    (A : Tensor (m :: ns)) (hA : StoresTensor memory inputBase (m :: ns) A)
    (hQblock : DisjointBlocks frameBase (m * stride) outputBase (q * suffixSize ns))
    (hAblock : DisjointBlocks inputBase (m * suffixSize ns) outputBase (q * suffixSize ns))
    (scratch : MatrixMultiplyScratch) {start : State Caller} {trace : Trace Caller}
    (ht : LegalTrace Caller start trace) (offset : ℕ)
    (hs : E.Relates (matrixMultiplyRowState
      (contractMultiplyData memory m q ns frameBase stride inputBase outputBase) 0 scratch) (trace.state offset)) :
    let p := contractMultiplyData memory m q ns frameBase stride inputBase outputBase
    let n := offset + matrixMultiplyReturnTime p
    (trace.state n).label = E.labels 21 ∧ (trace.state n).status = .running ∧
      StoresTensor (trace.state n).memory outputBase (q :: ns) (contract Q A) ∧
      StoresTensor (trace.state n).memory inputBase (m :: ns) A ∧
      StoresFrame (trace.state n).memory frameBase stride Q ∧
      (∀ address, ¬ (outputBase ≤ address ∧ address < outputBase + q * suffixSize ns) →
        (trace.state n).memory address = memory address) ∧
      CostThrough Caller trace n ≤ CostThrough Caller trace offset + 17 * (q + m + suffixSize ns + 1)^3 ∧
      (∀ j : Fin Caller.realRegisters, (∀ i, j ≠ E.reals i) →
        (trace.state n).real j = (trace.state offset).real j) ∧
      (∀ j : Fin (Caller.extraNatRegisters + 1), (∀ i, j ≠ E.naturals i) →
        (trace.state n).natural j = (trace.state offset).natural j) := by
  let p := contractMultiplyData memory m q ns frameBase stride inputBase outputBase
  have hsafe := contractMultiplyData_safe memory m q ns frameBase stride inputBase outputBase hq hQblock hAblock
  obtain ⟨hl, hstatus, hmat, ho, hc, hr, hn⟩ := E.matrixMultiply_product_at p hsafe scratch ht offset hs
  have hout : StoresTensor (trace.state (offset + matrixMultiplyReturnTime p)).memory
      outputBase (q :: ns) (contract Q A) := by
    apply (storesTensor_readMatrix_iff _ outputBase (contract Q A)).mpr
    exact hmat.trans (contractMultiplyData_product memory frameBase stride inputBase outputBase Q hQ A hA)
  refine ⟨hl, hstatus, hout, ?_, ?_, ho, hc, hr, hn⟩
  · apply hA.memory_eq
    intro address ha
    apply ho address
    apply disjointBlocks_not_mem_right hAblock
    simpa only [List.prod_cons, tensor_suffixSize_eq_prod] using ha
  · apply hQ.memory_eq hq
    intro address ha
    exact ho address (disjointBlocks_not_mem_right hQblock ha)

theorem RoutineEmbedding.lift_run_at {Caller : Program}
    (E : NLA.Proofs.TR04.RoutineEmbedding matrixMultiplyProgram Caller)
    {m q : ℕ} {ns : List ℕ} (memory : ℕ → ℝ)
    (frameBase stride inputBase outputBase : ℕ) (hq : q ≤ stride)
    (Q : Matrix (Fin m) (Fin q) ℝ) (hQ : StoresFrame memory frameBase stride Q)
    (A : Tensor (q :: ns)) (hA : StoresTensor memory inputBase (q :: ns) A)
    (hQblock : DisjointBlocks frameBase (m * stride) outputBase (m * suffixSize ns))
    (hAblock : DisjointBlocks inputBase (q * suffixSize ns) outputBase (m * suffixSize ns))
    (scratch : MatrixMultiplyScratch) {start : State Caller} {trace : Trace Caller}
    (ht : LegalTrace Caller start trace) (offset : ℕ)
    (hs : E.Relates (matrixMultiplyRowState
      (liftMultiplyData memory m q ns frameBase stride inputBase outputBase) 0 scratch) (trace.state offset)) :
    let p := liftMultiplyData memory m q ns frameBase stride inputBase outputBase
    let n := offset + matrixMultiplyReturnTime p
    (trace.state n).label = E.labels 21 ∧ (trace.state n).status = .running ∧
      StoresTensor (trace.state n).memory outputBase (m :: ns) (lift Q A) ∧
      StoresTensor (trace.state n).memory inputBase (q :: ns) A ∧
      StoresFrame (trace.state n).memory frameBase stride Q ∧
      (∀ address, ¬ (outputBase ≤ address ∧ address < outputBase + m * suffixSize ns) →
        (trace.state n).memory address = memory address) ∧
      CostThrough Caller trace n ≤ CostThrough Caller trace offset + 17 * (m + q + suffixSize ns + 1)^3 ∧
      (∀ j : Fin Caller.realRegisters, (∀ i, j ≠ E.reals i) →
        (trace.state n).real j = (trace.state offset).real j) ∧
      (∀ j : Fin (Caller.extraNatRegisters + 1), (∀ i, j ≠ E.naturals i) →
        (trace.state n).natural j = (trace.state offset).natural j) := by
  let p := liftMultiplyData memory m q ns frameBase stride inputBase outputBase
  have hsafe := liftMultiplyData_safe memory m q ns frameBase stride inputBase outputBase hq hQblock hAblock
  obtain ⟨hl, hstatus, hmat, ho, hc, hr, hn⟩ := E.matrixMultiply_product_at p hsafe scratch ht offset hs
  have hout : StoresTensor (trace.state (offset + matrixMultiplyReturnTime p)).memory
      outputBase (m :: ns) (lift Q A) := by
    apply (storesTensor_readMatrix_iff _ outputBase (lift Q A)).mpr
    exact hmat.trans (liftMultiplyData_product memory frameBase stride inputBase outputBase Q hQ A hA)
  refine ⟨hl, hstatus, hout, ?_, ?_, ho, hc, hr, hn⟩
  · apply hA.memory_eq
    intro address ha
    apply ho address
    apply disjointBlocks_not_mem_right hAblock
    simpa only [List.prod_cons, tensor_suffixSize_eq_prod] using ha
  · apply hQ.memory_eq hq
    intro address ha
    exact ho address (disjointBlocks_not_mem_right hQblock ha)

#assert_trust kernel RoutineEmbedding.contract_run_at
#assert_trust kernel RoutineEmbedding.lift_run_at
#print axioms RoutineEmbedding.contract_run_at
#print axioms RoutineEmbedding.lift_run_at
end NLA.Proofs.TR04
