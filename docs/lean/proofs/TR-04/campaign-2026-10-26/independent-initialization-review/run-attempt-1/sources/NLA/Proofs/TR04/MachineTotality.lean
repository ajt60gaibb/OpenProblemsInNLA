import NLA.Proofs.TR04.MachineExecution
import NLA.Proofs.TR04.SVDTotal

/-! Unconditional totality and legal traces for the actual unchanged machine.
This does not assert correctness, termination or polynomial cost of a solver. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

/-- Every state of every finite program has an actual charged successor,
including all rectangular SVD instructions and their empty dimensions. -/
theorem step_total (P : Program) (s : State P) :
    ∃ t : State P, Step P s t (charge P s) :=
  step_total_of_svd_total (fun _ _ B => SVD.exists_validSVD B) P s

/-- A legal trace exists independently of any approximation guarantee; no
nonexistence of SVD responses can make all-trace correctness vacuous. -/
theorem exists_legalTrace (P : Program) (start : State P) :
    ∃ trace : Trace P, LegalTrace P start trace :=
  exists_legalTrace_of_step_total P (step_total P) start

#assert_trust kernel step_total
#assert_trust kernel exists_legalTrace
#print axioms step_total
#print axioms exists_legalTrace
end NLA.Proofs.TR04
