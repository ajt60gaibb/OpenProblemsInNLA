import NLA.Proofs.TR04.MachineTensorMultiplyTrace
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
open NLA.Proofs.TR04 NLA.Proofs.TR04.TensorFormat NLA.Computation.SVDMachine
namespace TensorMultiplyExactConsumer

theorem literal_contract {Caller : Program}
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
        (trace.state n).natural j = (trace.state offset).natural j) :=
  E.contract_run_at memory frameBase stride inputBase outputBase hq Q hQ A hA hQblock hAblock scratch ht offset hs
#assert_trust kernel literal_contract

theorem literal_lift {Caller : Program}
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
        (trace.state n).natural j = (trace.state offset).natural j) :=
  E.lift_run_at memory frameBase stride inputBase outputBase hq Q hQ A hA hQblock hAblock scratch ht offset hs
#assert_trust kernel literal_lift

theorem literal_full_U_prefix_contract {Caller : Program}
    (E : NLA.Proofs.TR04.RoutineEmbedding matrixMultiplyProgram Caller)
    {m q : ℕ} {ns : List ℕ} (memory : ℕ → ℝ)
    (frameBase inputBase outputBase : ℕ) (hq : q ≤ m)
    (U : Matrix (Fin m) (Fin m) ℝ) (hU : readMatrix memory m m frameBase = U)
    (A : Tensor (m :: ns)) (hA : StoresTensor memory inputBase (m :: ns) A)
    (hQblock : DisjointBlocks frameBase (m * m) outputBase (q * suffixSize ns))
    (hAblock : DisjointBlocks inputBase (m * suffixSize ns) outputBase (q * suffixSize ns))
    (scratch : MatrixMultiplyScratch) {start : State Caller} {trace : Trace Caller}
    (ht : LegalTrace Caller start trace) (offset : ℕ)
    (hs : E.Relates (matrixMultiplyRowState
      (contractMultiplyData memory m q ns frameBase m inputBase outputBase) 0 scratch) (trace.state offset)) :
    let p := contractMultiplyData memory m q ns frameBase m inputBase outputBase
    let n := offset + matrixMultiplyReturnTime p
    (trace.state n).label = E.labels 21 ∧ (trace.state n).status = .running ∧
      StoresTensor (trace.state n).memory outputBase (q :: ns) (contract (U.submatrix id (Fin.castLE hq)) A) ∧
      StoresTensor (trace.state n).memory inputBase (m :: ns) A ∧
      StoresFrame (trace.state n).memory frameBase m (U.submatrix id (Fin.castLE hq)) ∧
      (∀ address, ¬ (outputBase ≤ address ∧ address < outputBase + q * suffixSize ns) →
        (trace.state n).memory address = memory address) ∧
      CostThrough Caller trace n ≤ CostThrough Caller trace offset + 17 * (q + m + suffixSize ns + 1)^3 ∧
      (∀ j : Fin Caller.realRegisters, (∀ i, j ≠ E.reals i) →
        (trace.state n).real j = (trace.state offset).real j) ∧
      (∀ j : Fin (Caller.extraNatRegisters + 1), (∀ i, j ≠ E.naturals i) →
        (trace.state n).natural j = (trace.state offset).natural j) :=
  E.contract_run_at memory frameBase m inputBase outputBase hq (U.submatrix id (Fin.castLE hq))
    (storesFrame_prefix memory frameBase U hq hU) A hA hQblock hAblock scratch ht offset hs
#assert_trust kernel literal_full_U_prefix_contract

theorem literal_dense_Q_lift {Caller : Program}
    (E : NLA.Proofs.TR04.RoutineEmbedding matrixMultiplyProgram Caller)
    {m q : ℕ} {ns : List ℕ} (memory : ℕ → ℝ)
    (frameBase inputBase outputBase : ℕ)
    (Q : Matrix (Fin m) (Fin q) ℝ) (hQ : readMatrix memory m q frameBase = Q)
    (A : Tensor (q :: ns)) (hA : StoresTensor memory inputBase (q :: ns) A)
    (hQblock : DisjointBlocks frameBase (m * q) outputBase (m * suffixSize ns))
    (hAblock : DisjointBlocks inputBase (q * suffixSize ns) outputBase (m * suffixSize ns))
    (scratch : MatrixMultiplyScratch) {start : State Caller} {trace : Trace Caller}
    (ht : LegalTrace Caller start trace) (offset : ℕ)
    (hs : E.Relates (matrixMultiplyRowState
      (liftMultiplyData memory m q ns frameBase q inputBase outputBase) 0 scratch) (trace.state offset)) :
    let p := liftMultiplyData memory m q ns frameBase q inputBase outputBase
    let n := offset + matrixMultiplyReturnTime p
    (trace.state n).label = E.labels 21 ∧ (trace.state n).status = .running ∧
      StoresTensor (trace.state n).memory outputBase (m :: ns) (lift Q A) ∧
      StoresTensor (trace.state n).memory inputBase (q :: ns) A ∧
      StoresFrame (trace.state n).memory frameBase q Q ∧
      (∀ address, ¬ (outputBase ≤ address ∧ address < outputBase + m * suffixSize ns) →
        (trace.state n).memory address = memory address) ∧
      CostThrough Caller trace n ≤ CostThrough Caller trace offset + 17 * (m + q + suffixSize ns + 1)^3 ∧
      (∀ j : Fin Caller.realRegisters, (∀ i, j ≠ E.reals i) →
        (trace.state n).real j = (trace.state offset).real j) ∧
      (∀ j : Fin (Caller.extraNatRegisters + 1), (∀ i, j ≠ E.naturals i) →
        (trace.state n).natural j = (trace.state offset).natural j) :=
  E.lift_run_at memory frameBase q inputBase outputBase le_rfl Q
    ((storesFrame_dense_iff memory frameBase Q).mpr hQ) A hA hQblock hAblock scratch ht offset hs
#assert_trust kernel literal_dense_Q_lift
end TensorMultiplyExactConsumer
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.StoresTensor
#print axioms NLA.Proofs.TR04.TensorFormat.StoresTensor
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.StoresFrame
#print axioms NLA.Proofs.TR04.TensorFormat.StoresFrame
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.tensor_suffixSize_eq_prod
#print axioms NLA.Proofs.TR04.TensorFormat.tensor_suffixSize_eq_prod
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixOffset_radixSuffixEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.radixOffset_radixSuffixEquiv
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.storesTensor_iff_flat
#print axioms NLA.Proofs.TR04.TensorFormat.storesTensor_iff_flat
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.storesTensor_readMatrix_iff
#print axioms NLA.Proofs.TR04.TensorFormat.storesTensor_readMatrix_iff
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixDenseFirst_actFirst
#print axioms NLA.Proofs.TR04.TensorFormat.radixDenseFirst_actFirst
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixOffset_merge_indices
#print axioms NLA.Proofs.TR04.TensorFormat.radixOffset_merge_indices
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.storesTensor_merge_iff
#print axioms NLA.Proofs.TR04.TensorFormat.storesTensor_merge_iff
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.storesTensor_unmerge_iff
#print axioms NLA.Proofs.TR04.TensorFormat.storesTensor_unmerge_iff
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.StoresTensor.memory_eq
#print axioms NLA.Proofs.TR04.TensorFormat.StoresTensor.memory_eq
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.storesFrame_dense_iff
#print axioms NLA.Proofs.TR04.TensorFormat.storesFrame_dense_iff
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.storesFrame_prefix
#print axioms NLA.Proofs.TR04.TensorFormat.storesFrame_prefix
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.StoresFrame.memory_eq
#print axioms NLA.Proofs.TR04.TensorFormat.StoresFrame.memory_eq
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.storesTensor_original
#print axioms NLA.Proofs.TR04.TensorFormat.storesTensor_original
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actMultiplyData
#print axioms NLA.Proofs.TR04.TensorFormat.actMultiplyData
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.contractMultiplyData
#print axioms NLA.Proofs.TR04.TensorFormat.contractMultiplyData
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.liftMultiplyData
#print axioms NLA.Proofs.TR04.TensorFormat.liftMultiplyData
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actMultiplyData_left
#print axioms NLA.Proofs.TR04.TensorFormat.actMultiplyData_left
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actMultiplyData_right
#print axioms NLA.Proofs.TR04.TensorFormat.actMultiplyData_right
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.actMultiplyData_product
#print axioms NLA.Proofs.TR04.TensorFormat.actMultiplyData_product
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.contractMultiplyData_product
#print axioms NLA.Proofs.TR04.TensorFormat.contractMultiplyData_product
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.liftMultiplyData_product
#print axioms NLA.Proofs.TR04.TensorFormat.liftMultiplyData_product
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.contractMultiplyData_safe
#print axioms NLA.Proofs.TR04.TensorFormat.contractMultiplyData_safe
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.liftMultiplyData_safe
#print axioms NLA.Proofs.TR04.TensorFormat.liftMultiplyData_safe
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.contract_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.contract_run_at
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.lift_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.lift_run_at
