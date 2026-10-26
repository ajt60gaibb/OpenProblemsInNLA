import NLA.Proofs.TR04.MachineTTStageChildSVD
import NLA.Proofs.TR04.TTRecursiveBudget

/-! Result certificate for the actual shared stage continuation. This is a
statement of stored execution facts; the recursive execution theorem must
construct it from the literal program. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat

structure TTCoreResult (old final : State ttProgram) (L : Layout) (level m q n : ℕ)
    (ns : List ℕ) (r : ℕ → ℕ) (Q : Matrix (Fin m) (Fin q) ℝ)
    (A : Tensor (m::n::ns)) (Z : Tensor ((q*n)::ns)) : Prop where
  childCompletion : Completion ((q*n)::ns) (fun j => r (j+1)) (merge q n ns (contract Q A)) Z
  label : final.label=(if level=0 then 349 else 287)
  running : final.status=.running
  levelValue : final.natural 84=level-1
  currentStored : StoresTensor final.memory (final.natural 89) (m::n::ns) (lift Q ((merge q n ns).symm Z))
  workPair : TTWorkPair L final
  preserves : TTStagePreserves L level old final
  allocation : TTAllocationRegisters L final
  candidatePointer : level=0 → final.natural 123=old.natural 71+old.natural 76*old.natural 64

 theorem TTCoreResult.prefixCompletion {old final : State ttProgram} {L : Layout}
    {level m n : ℕ} {ns : List ℕ} {r : ℕ → ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m (suffixSize (n::ns))) → ℝ}
    {V : Matrix (Fin (suffixSize (n::ns))) (Fin (suffixSize (n::ns))) ℝ}
    {A : Tensor (m::n::ns)} {Z : Tensor ((stepRank m (n::ns) r*n)::ns)}
    (h : TTCoreResult old final L level m (stepRank m (n::ns) r) n ns r (stepFrame (n::ns) r U) A Z)
    (hSVD : ValidSVD (radixDenseFirst A) U sigma V) :
    Completion (m::n::ns) r A (stepOutput r U Z) :=
  completion_step_radix hSVD h.childCompletion

#assert_trust kernel TTCoreResult
#assert_trust kernel TTCoreResult.prefixCompletion
#print axioms TTCoreResult.prefixCompletion
end NLA.Proofs.TR04
