import NLA.Proofs.RE06.RepairMajorant
import NLA.Statements.RE06
import Reviewed.RE06
set_option autoImplicit false
set_option leancert.trust "kernel"
open Lean Elab Command in
elab "#repair_theorem " n:ident : command => do
  let d ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  match (← getEnv).find? d with
  | some (.thmInfo _) => pure ()
  | _ => throwErrorAt n "expected actual theorem declaration"
namespace NLA.Proofs.RE06.RepairAudit
 theorem live_frozen_identity : NLA.Statements.RE06.Target =
    NLA.ReviewedStatements.RE06.Target := rfl
end NLA.Proofs.RE06.RepairAudit

#repair_theorem NLA.Proofs.RE06.Repair.squaredFrobenius_zero_nonneg
#assert_trust kernel NLA.Proofs.RE06.Repair.squaredFrobenius_zero_nonneg
#print axioms NLA.Proofs.RE06.Repair.squaredFrobenius_zero_nonneg

#repair_theorem NLA.Proofs.RE06.Repair.squaredFrobenius_sub_zero
#assert_trust kernel NLA.Proofs.RE06.Repair.squaredFrobenius_sub_zero
#print axioms NLA.Proofs.RE06.Repair.squaredFrobenius_sub_zero

#repair_theorem NLA.Proofs.RE06.Repair.squaredFrobenius_pythagoras
#assert_trust kernel NLA.Proofs.RE06.Repair.squaredFrobenius_pythagoras
#print axioms NLA.Proofs.RE06.Repair.squaredFrobenius_pythagoras

#repair_theorem NLA.Proofs.RE06.Repair.rangeResidual_orthogonal
#assert_trust kernel NLA.Proofs.RE06.Repair.rangeResidual_orthogonal
#print axioms NLA.Proofs.RE06.Repair.rangeResidual_orthogonal

#repair_theorem NLA.Proofs.RE06.Repair.rangeResidual_pythagoras
#assert_trust kernel NLA.Proofs.RE06.Repair.rangeResidual_pythagoras
#print axioms NLA.Proofs.RE06.Repair.rangeResidual_pythagoras

#repair_theorem NLA.Proofs.RE06.Repair.rangeResidual_minimizes
#assert_trust kernel NLA.Proofs.RE06.Repair.rangeResidual_minimizes
#print axioms NLA.Proofs.RE06.Repair.rangeResidual_minimizes

#repair_theorem NLA.Proofs.RE06.Repair.rangeResidual_le_range_approximation
#assert_trust kernel NLA.Proofs.RE06.Repair.rangeResidual_le_range_approximation
#print axioms NLA.Proofs.RE06.Repair.rangeResidual_le_range_approximation

#repair_theorem NLA.Proofs.RE06.Repair.squaredFrobenius_row_pythagoras
#assert_trust kernel NLA.Proofs.RE06.Repair.squaredFrobenius_row_pythagoras
#print axioms NLA.Proofs.RE06.Repair.squaredFrobenius_row_pythagoras

#repair_theorem NLA.Proofs.RE06.Repair.rangefinder_error
#assert_trust kernel NLA.Proofs.RE06.Repair.rangefinder_error
#print axioms NLA.Proofs.RE06.Repair.rangefinder_error

#repair_theorem NLA.Proofs.RE06.Repair.rangefinder_majorant
#assert_trust kernel NLA.Proofs.RE06.Repair.rangefinder_majorant
#print axioms NLA.Proofs.RE06.Repair.rangefinder_majorant

#repair_theorem NLA.Proofs.RE06.Repair.full_column_pseudoinverse_mul
#assert_trust kernel NLA.Proofs.RE06.Repair.full_column_pseudoinverse_mul
#print axioms NLA.Proofs.RE06.Repair.full_column_pseudoinverse_mul

#repair_theorem NLA.Proofs.RE06.Repair.regression_coefficients
#assert_trust kernel NLA.Proofs.RE06.Repair.regression_coefficients
#print axioms NLA.Proofs.RE06.Repair.regression_coefficients

#repair_theorem NLA.Proofs.RE06.Repair.regression_error_decomposition
#assert_trust kernel NLA.Proofs.RE06.Repair.regression_error_decomposition
#print axioms NLA.Proofs.RE06.Repair.regression_error_decomposition

#repair_theorem NLA.Proofs.RE06.Repair.regression_error_energy
#assert_trust kernel NLA.Proofs.RE06.Repair.regression_error_energy
#print axioms NLA.Proofs.RE06.Repair.regression_error_energy

#repair_theorem NLA.Proofs.RE06.Repair.actual_repair_error_energy
#assert_trust kernel NLA.Proofs.RE06.Repair.actual_repair_error_energy
#print axioms NLA.Proofs.RE06.Repair.actual_repair_error_energy

#repair_theorem NLA.Proofs.RE06.Repair.excessMajorant_nonneg
#assert_trust kernel NLA.Proofs.RE06.Repair.excessMajorant_nonneg
#print axioms NLA.Proofs.RE06.Repair.excessMajorant_nonneg

#repair_theorem NLA.Proofs.RE06.Repair.actual_repair_majorant
#assert_trust kernel NLA.Proofs.RE06.Repair.actual_repair_majorant
#print axioms NLA.Proofs.RE06.Repair.actual_repair_majorant

#repair_theorem NLA.Proofs.RE06.Repair.sketchRepair_residual_identity
#assert_trust kernel NLA.Proofs.RE06.Repair.sketchRepair_residual_identity
#print axioms NLA.Proofs.RE06.Repair.sketchRepair_residual_identity
