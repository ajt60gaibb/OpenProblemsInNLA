import NLA.Proofs.TR04.Feasible
import NLA.Proofs.TR04.MachineExecution
import NLA.Proofs.TR04.MachineTotality
import NLA.Proofs.TR04.MachineTraceBounds
import NLA.Proofs.TR04.Optimum
import NLA.Proofs.TR04.Reshape
import NLA.Proofs.TR04.ReshapeFrobenius
import NLA.Proofs.TR04.SVDCore
import NLA.Proofs.TR04.SVDTotal
import Reviewed.TR04
set_option autoImplicit false
set_option leancert.trust "kernel"
open Lean Elab Command in
elab "#assert_kind " n:ident expected:str : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let some info := (← getEnv).find? decl | throwErrorAt n "missing actual constant"
  match expected.getString, info with
  | "theorem", .thmInfo _ => pure ()
  | "definition", .defnInfo _ => pure ()
  | "inductive", .inductInfo _ => pure ()
  | _, _ => throwErrorAt n "constant kind differs from frozen source"
  logInfo m!"AUDITED_KIND {decl} {expected.getString}"
#assert_kind NLA.Computation.SVDMachine.Instruction "inductive"
#assert_trust kernel NLA.Computation.SVDMachine.Instruction
#print axioms NLA.Computation.SVDMachine.Instruction
#assert_kind NLA.Computation.SVDMachine.Program "inductive"
#assert_trust kernel NLA.Computation.SVDMachine.Program
#print axioms NLA.Computation.SVDMachine.Program
#assert_kind NLA.Computation.SVDMachine.Status "inductive"
#assert_trust kernel NLA.Computation.SVDMachine.Status
#print axioms NLA.Computation.SVDMachine.Status
#assert_kind NLA.Computation.SVDMachine.State "inductive"
#assert_trust kernel NLA.Computation.SVDMachine.State
#print axioms NLA.Computation.SVDMachine.State
#assert_kind NLA.Computation.SVDMachine.initial "definition"
#assert_trust kernel NLA.Computation.SVDMachine.initial
#print axioms NLA.Computation.SVDMachine.initial
#assert_kind NLA.Computation.SVDMachine.ordinaryStep "definition"
#assert_trust kernel NLA.Computation.SVDMachine.ordinaryStep
#print axioms NLA.Computation.SVDMachine.ordinaryStep
#assert_kind NLA.Computation.SVDMachine.ValidSVD "definition"
#assert_trust kernel NLA.Computation.SVDMachine.ValidSVD
#print axioms NLA.Computation.SVDMachine.ValidSVD
#assert_kind NLA.Computation.SVDMachine.DisjointBlocks "definition"
#assert_trust kernel NLA.Computation.SVDMachine.DisjointBlocks
#print axioms NLA.Computation.SVDMachine.DisjointBlocks
#assert_kind NLA.Computation.SVDMachine.OutputBlocksDisjoint "definition"
#assert_trust kernel NLA.Computation.SVDMachine.OutputBlocksDisjoint
#print axioms NLA.Computation.SVDMachine.OutputBlocksDisjoint
#assert_kind NLA.Computation.SVDMachine.matrixCell "definition"
#assert_trust kernel NLA.Computation.SVDMachine.matrixCell
#print axioms NLA.Computation.SVDMachine.matrixCell
#assert_kind NLA.Computation.SVDMachine.readMatrix "definition"
#assert_trust kernel NLA.Computation.SVDMachine.readMatrix
#print axioms NLA.Computation.SVDMachine.readMatrix
#assert_kind NLA.Computation.SVDMachine.writeSVD "definition"
#assert_trust kernel NLA.Computation.SVDMachine.writeSVD
#print axioms NLA.Computation.SVDMachine.writeSVD
#assert_kind NLA.Computation.SVDMachine.charge "definition"
#assert_trust kernel NLA.Computation.SVDMachine.charge
#print axioms NLA.Computation.SVDMachine.charge
#assert_kind NLA.Computation.SVDMachine.Step "definition"
#assert_trust kernel NLA.Computation.SVDMachine.Step
#print axioms NLA.Computation.SVDMachine.Step
#assert_kind NLA.Computation.SVDMachine.Trace "inductive"
#assert_trust kernel NLA.Computation.SVDMachine.Trace
#print axioms NLA.Computation.SVDMachine.Trace
#assert_kind NLA.Computation.SVDMachine.LegalTrace "definition"
#assert_trust kernel NLA.Computation.SVDMachine.LegalTrace
#print axioms NLA.Computation.SVDMachine.LegalTrace
#assert_kind NLA.Computation.SVDMachine.CostThrough "definition"
#assert_trust kernel NLA.Computation.SVDMachine.CostThrough
#print axioms NLA.Computation.SVDMachine.CostThrough
#assert_kind NLA.Computation.TensorTrainApproximation.Shape "inductive"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Shape
#print axioms NLA.Computation.TensorTrainApproximation.Shape
#assert_kind NLA.Computation.TensorTrainApproximation.Index "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Index
#print axioms NLA.Computation.TensorTrainApproximation.Index
#assert_kind NLA.Computation.TensorTrainApproximation.Tensor "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Tensor
#print axioms NLA.Computation.TensorTrainApproximation.Tensor
#assert_kind NLA.Computation.TensorTrainApproximation.Cut "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Cut
#print axioms NLA.Computation.TensorTrainApproximation.Cut
#assert_kind NLA.Computation.TensorTrainApproximation.Ranks "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Ranks
#print axioms NLA.Computation.TensorTrainApproximation.Ranks
#assert_kind NLA.Computation.TensorTrainApproximation.RowIndex "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.RowIndex
#print axioms NLA.Computation.TensorTrainApproximation.RowIndex
#assert_kind NLA.Computation.TensorTrainApproximation.ColIndex "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.ColIndex
#print axioms NLA.Computation.TensorTrainApproximation.ColIndex
#assert_kind NLA.Computation.TensorTrainApproximation.join "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.join
#print axioms NLA.Computation.TensorTrainApproximation.join
#assert_kind NLA.Computation.TensorTrainApproximation.Unfold "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Unfold
#print axioms NLA.Computation.TensorTrainApproximation.Unfold
#assert_kind NLA.Computation.TensorTrainApproximation.Feasible "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Feasible
#print axioms NLA.Computation.TensorTrainApproximation.Feasible
#assert_kind NLA.Computation.TensorTrainApproximation.FrobeniusSq "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.FrobeniusSq
#print axioms NLA.Computation.TensorTrainApproximation.FrobeniusSq
#assert_kind NLA.Computation.TensorTrainApproximation.Optimum "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Optimum
#print axioms NLA.Computation.TensorTrainApproximation.Optimum
#assert_kind NLA.Computation.TensorTrainApproximation.DenseSize "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.DenseSize
#print axioms NLA.Computation.TensorTrainApproximation.DenseSize
#assert_kind NLA.Computation.TensorTrainApproximation.SuffixSize "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.SuffixSize
#print axioms NLA.Computation.TensorTrainApproximation.SuffixSize
#assert_kind NLA.Computation.TensorTrainApproximation.Offset "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Offset
#print axioms NLA.Computation.TensorTrainApproximation.Offset
#assert_kind NLA.Computation.TensorTrainApproximation.Decode "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Decode
#print axioms NLA.Computation.TensorTrainApproximation.Decode
#assert_kind NLA.Computation.TensorTrainApproximation.InputMemory "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.InputMemory
#print axioms NLA.Computation.TensorTrainApproximation.InputMemory
#assert_kind NLA.Computation.TensorTrainApproximation.Start "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Start
#print axioms NLA.Computation.TensorTrainApproximation.Start
#assert_kind NLA.Computation.TensorTrainApproximation.Returns "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Returns
#print axioms NLA.Computation.TensorTrainApproximation.Returns
#assert_kind NLA.Computation.TensorTrainApproximation.Size "definition"
#assert_trust kernel NLA.Computation.TensorTrainApproximation.Size
#print axioms NLA.Computation.TensorTrainApproximation.Size
#assert_kind NLA.Proofs.TR04.splitIndex "definition"
#assert_trust kernel NLA.Proofs.TR04.splitIndex
#print axioms NLA.Proofs.TR04.splitIndex
#assert_kind NLA.Proofs.TR04.splitIndex_join "theorem"
#assert_trust kernel NLA.Proofs.TR04.splitIndex_join
#print axioms NLA.Proofs.TR04.splitIndex_join
#assert_kind NLA.Proofs.TR04.join_splitIndex "theorem"
#assert_trust kernel NLA.Proofs.TR04.join_splitIndex
#print axioms NLA.Proofs.TR04.join_splitIndex
#assert_kind NLA.Proofs.TR04.joinEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.joinEquiv
#print axioms NLA.Proofs.TR04.joinEquiv
#assert_kind NLA.Proofs.TR04.unfoldLinearEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.unfoldLinearEquiv
#print axioms NLA.Proofs.TR04.unfoldLinearEquiv
#assert_kind NLA.Proofs.TR04.unfoldContinuousLinearEquiv "definition"
#assert_trust kernel NLA.Proofs.TR04.unfoldContinuousLinearEquiv
#print axioms NLA.Proofs.TR04.unfoldContinuousLinearEquiv
#assert_kind NLA.Proofs.TR04.unfoldLinearEquiv_apply "theorem"
#assert_trust kernel NLA.Proofs.TR04.unfoldLinearEquiv_apply
#print axioms NLA.Proofs.TR04.unfoldLinearEquiv_apply
#assert_kind NLA.Proofs.TR04.unfoldContinuousLinearEquiv_apply "theorem"
#assert_trust kernel NLA.Proofs.TR04.unfoldContinuousLinearEquiv_apply
#print axioms NLA.Proofs.TR04.unfoldContinuousLinearEquiv_apply
#assert_kind NLA.Proofs.TR04.continuous_unfold "theorem"
#assert_trust kernel NLA.Proofs.TR04.continuous_unfold
#print axioms NLA.Proofs.TR04.continuous_unfold
#assert_kind NLA.Proofs.TR04.unfold_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.unfold_zero
#print axioms NLA.Proofs.TR04.unfold_zero
#assert_kind NLA.Proofs.TR04.unfold_add "theorem"
#assert_trust kernel NLA.Proofs.TR04.unfold_add
#print axioms NLA.Proofs.TR04.unfold_add
#assert_kind NLA.Proofs.TR04.unfold_smul "theorem"
#assert_trust kernel NLA.Proofs.TR04.unfold_smul
#print axioms NLA.Proofs.TR04.unfold_smul
#assert_kind NLA.Proofs.TR04.unfold_injective "theorem"
#assert_trust kernel NLA.Proofs.TR04.unfold_injective
#print axioms NLA.Proofs.TR04.unfold_injective
#assert_kind NLA.Proofs.TR04.feasible_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.feasible_zero
#print axioms NLA.Proofs.TR04.feasible_zero
#assert_kind NLA.Proofs.TR04.feasible_nonempty "theorem"
#assert_trust kernel NLA.Proofs.TR04.feasible_nonempty
#print axioms NLA.Proofs.TR04.feasible_nonempty
#assert_kind NLA.Proofs.TR04.isClosed_matrix_rank_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.isClosed_matrix_rank_le
#print axioms NLA.Proofs.TR04.isClosed_matrix_rank_le
#assert_kind NLA.Proofs.TR04.isClosed_feasible "theorem"
#assert_trust kernel NLA.Proofs.TR04.isClosed_feasible
#print axioms NLA.Proofs.TR04.isClosed_feasible
#assert_kind NLA.Statements.TR04.Target "definition"
#assert_trust kernel NLA.Statements.TR04.Target
#print axioms NLA.Statements.TR04.Target
#assert_kind NLA.Proofs.TR04.step_cost_eq "theorem"
#assert_trust kernel NLA.Proofs.TR04.step_cost_eq
#print axioms NLA.Proofs.TR04.step_cost_eq
#assert_kind NLA.Proofs.TR04.step_of_halted "theorem"
#assert_trust kernel NLA.Proofs.TR04.step_of_halted
#print axioms NLA.Proofs.TR04.step_of_halted
#assert_kind NLA.Proofs.TR04.step_of_failed "theorem"
#assert_trust kernel NLA.Proofs.TR04.step_of_failed
#print axioms NLA.Proofs.TR04.step_of_failed
#assert_kind NLA.Proofs.TR04.exists_legalTrace_of_step_total "theorem"
#assert_trust kernel NLA.Proofs.TR04.exists_legalTrace_of_step_total
#print axioms NLA.Proofs.TR04.exists_legalTrace_of_step_total
#assert_kind NLA.Proofs.TR04.step_total_of_svd_total "theorem"
#assert_trust kernel NLA.Proofs.TR04.step_total_of_svd_total
#print axioms NLA.Proofs.TR04.step_total_of_svd_total
#assert_kind NLA.Proofs.TR04.exists_legalTrace_of_svd_total "theorem"
#assert_trust kernel NLA.Proofs.TR04.exists_legalTrace_of_svd_total
#print axioms NLA.Proofs.TR04.exists_legalTrace_of_svd_total
#assert_kind NLA.Proofs.TR04.SVD.Space "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.Space
#print axioms NLA.Proofs.TR04.SVD.Space
#assert_kind NLA.Proofs.TR04.SVD.rightBasis "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.rightBasis
#print axioms NLA.Proofs.TR04.SVD.rightBasis
#assert_kind NLA.Proofs.TR04.SVD.norm_image_rightBasis "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.norm_image_rightBasis
#print axioms NLA.Proofs.TR04.SVD.norm_image_rightBasis
#assert_kind NLA.Proofs.TR04.SVD.inner_image_rightBasis "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.inner_image_rightBasis
#print axioms NLA.Proofs.TR04.SVD.inner_image_rightBasis
#assert_kind NLA.Proofs.TR04.SVD.image_rightBasis_eq_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.image_rightBasis_eq_zero
#print axioms NLA.Proofs.TR04.SVD.image_rightBasis_eq_zero
#assert_kind NLA.Proofs.TR04.SVD.range_finrank_le_domain "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.range_finrank_le_domain
#print axioms NLA.Proofs.TR04.SVD.range_finrank_le_domain
#assert_kind NLA.Proofs.TR04.SVD.range_finrank_le_codomain "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.range_finrank_le_codomain
#print axioms NLA.Proofs.TR04.SVD.range_finrank_le_codomain
#assert_kind NLA.Proofs.TR04.SVD.leftVector "definition"
#assert_trust kernel NLA.Proofs.TR04.SVD.leftVector
#print axioms NLA.Proofs.TR04.SVD.leftVector
#assert_kind NLA.Proofs.TR04.SVD.orthonormal_leftVector_positive "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormal_leftVector_positive
#print axioms NLA.Proofs.TR04.SVD.orthonormal_leftVector_positive
#assert_kind NLA.Proofs.TR04.SVD.exists_leftBasis "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_leftBasis
#print axioms NLA.Proofs.TR04.SVD.exists_leftBasis
#assert_kind NLA.Proofs.TR04.SVD.image_rightBasis_eq_smul "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.image_rightBasis_eq_smul
#print axioms NLA.Proofs.TR04.SVD.image_rightBasis_eq_smul
#assert_kind NLA.Proofs.TR04.SVD.sum_fin_truncate "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_fin_truncate
#print axioms NLA.Proofs.TR04.SVD.sum_fin_truncate
#assert_kind NLA.Proofs.TR04.SVD.exists_validSVD "theorem"
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_validSVD
#print axioms NLA.Proofs.TR04.SVD.exists_validSVD
#assert_kind NLA.Proofs.TR04.step_total "theorem"
#assert_trust kernel NLA.Proofs.TR04.step_total
#print axioms NLA.Proofs.TR04.step_total
#assert_kind NLA.Proofs.TR04.exists_legalTrace "theorem"
#assert_trust kernel NLA.Proofs.TR04.exists_legalTrace
#print axioms NLA.Proofs.TR04.exists_legalTrace
#assert_kind NLA.Proofs.TR04.legalTrace_cost_eq "theorem"
#assert_trust kernel NLA.Proofs.TR04.legalTrace_cost_eq
#print axioms NLA.Proofs.TR04.legalTrace_cost_eq
#assert_kind NLA.Proofs.TR04.costThrough_zero "theorem"
#assert_trust kernel NLA.Proofs.TR04.costThrough_zero
#print axioms NLA.Proofs.TR04.costThrough_zero
#assert_kind NLA.Proofs.TR04.costThrough_succ "theorem"
#assert_trust kernel NLA.Proofs.TR04.costThrough_succ
#print axioms NLA.Proofs.TR04.costThrough_succ
#assert_kind NLA.Proofs.TR04.charge_pos_of_running "theorem"
#assert_trust kernel NLA.Proofs.TR04.charge_pos_of_running
#print axioms NLA.Proofs.TR04.charge_pos_of_running
#assert_kind NLA.Proofs.TR04.legalTrace_halted_state_add "theorem"
#assert_trust kernel NLA.Proofs.TR04.legalTrace_halted_state_add
#print axioms NLA.Proofs.TR04.legalTrace_halted_state_add
#assert_kind NLA.Proofs.TR04.costThrough_add_of_halted "theorem"
#assert_trust kernel NLA.Proofs.TR04.costThrough_add_of_halted
#print axioms NLA.Proofs.TR04.costThrough_add_of_halted
#assert_kind NLA.Proofs.TR04.continuous_frobeniusSq "theorem"
#assert_trust kernel NLA.Proofs.TR04.continuous_frobeniusSq
#print axioms NLA.Proofs.TR04.continuous_frobeniusSq
#assert_kind NLA.Proofs.TR04.frobeniusSq_nonneg "theorem"
#assert_trust kernel NLA.Proofs.TR04.frobeniusSq_nonneg
#print axioms NLA.Proofs.TR04.frobeniusSq_nonneg
#assert_kind NLA.Proofs.TR04.frobeniusSq_coordinate_le "theorem"
#assert_trust kernel NLA.Proofs.TR04.frobeniusSq_coordinate_le
#print axioms NLA.Proofs.TR04.frobeniusSq_coordinate_le
#assert_kind NLA.Proofs.TR04.frobeniusSq_self "theorem"
#assert_trust kernel NLA.Proofs.TR04.frobeniusSq_self
#print axioms NLA.Proofs.TR04.frobeniusSq_self
#assert_kind NLA.Proofs.TR04.frobeniusSq_eq_zero_iff "theorem"
#assert_trust kernel NLA.Proofs.TR04.frobeniusSq_eq_zero_iff
#print axioms NLA.Proofs.TR04.frobeniusSq_eq_zero_iff
#assert_kind NLA.Proofs.TR04.frobeniusSq_sublevel_subset_box "theorem"
#assert_trust kernel NLA.Proofs.TR04.frobeniusSq_sublevel_subset_box
#print axioms NLA.Proofs.TR04.frobeniusSq_sublevel_subset_box
#assert_kind NLA.Proofs.TR04.exists_feasible_minimizer "theorem"
#assert_trust kernel NLA.Proofs.TR04.exists_feasible_minimizer
#print axioms NLA.Proofs.TR04.exists_feasible_minimizer
#assert_kind NLA.Proofs.TR04.exists_optimum "theorem"
#assert_trust kernel NLA.Proofs.TR04.exists_optimum
#print axioms NLA.Proofs.TR04.exists_optimum
#assert_kind NLA.Proofs.TR04.optimum_nonneg "theorem"
#assert_trust kernel NLA.Proofs.TR04.optimum_nonneg
#print axioms NLA.Proofs.TR04.optimum_nonneg
#assert_kind NLA.Proofs.TR04.optimum_le_of_feasible "theorem"
#assert_trust kernel NLA.Proofs.TR04.optimum_le_of_feasible
#print axioms NLA.Proofs.TR04.optimum_le_of_feasible
#assert_kind NLA.Proofs.TR04.optimum_eq_zero_iff_feasible "theorem"
#assert_trust kernel NLA.Proofs.TR04.optimum_eq_zero_iff_feasible
#print axioms NLA.Proofs.TR04.optimum_eq_zero_iff_feasible
#assert_kind NLA.Proofs.TR04.sum_unfold_indices "theorem"
#assert_trust kernel NLA.Proofs.TR04.sum_unfold_indices
#print axioms NLA.Proofs.TR04.sum_unfold_indices
#assert_kind NLA.Proofs.TR04.frobeniusSq_eq_unfold_sum "theorem"
#assert_trust kernel NLA.Proofs.TR04.frobeniusSq_eq_unfold_sum
#print axioms NLA.Proofs.TR04.frobeniusSq_eq_unfold_sum
#assert_kind NLA.ReviewedStatements.TR04.Target "definition"
#assert_trust kernel NLA.ReviewedStatements.TR04.Target
#print axioms NLA.ReviewedStatements.TR04.Target

noncomputable section
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
example : NLA.Statements.TR04.Target = NLA.ReviewedStatements.TR04.Target := rfl
example (m l : ℕ) (B : Matrix (Fin m) (Fin l) ℝ) :
    ∃ U sigma V, ValidSVD B U sigma V := NLA.Proofs.TR04.SVD.exists_validSVD B
example (l : ℕ) (B : Matrix (Fin 0) (Fin l) ℝ) :
    ∃ U sigma V, ValidSVD B U sigma V := NLA.Proofs.TR04.SVD.exists_validSVD B
example (m : ℕ) (B : Matrix (Fin m) (Fin 0) ℝ) :
    ∃ U sigma V, ValidSVD B U sigma V := NLA.Proofs.TR04.SVD.exists_validSVD B
example (S : Shape) (r : Ranks S) (A : Tensor S) :
    ∃ X : Tensor S, Feasible S r X ∧ Optimum S r A = FrobeniusSq S A X :=
  NLA.Proofs.TR04.exists_optimum S r A
example (S : Shape) (r : Ranks S) (A : Tensor S) :
    Optimum S r A = 0 ↔ Feasible S r A := NLA.Proofs.TR04.optimum_eq_zero_iff_feasible S r A
example (P : Program) (s : State P) : ∃ t : State P, Step P s t (charge P s) :=
  NLA.Proofs.TR04.step_total P s
example (P : Program) (start : State P) : ∃ trace : Trace P, LegalTrace P start trace :=
  NLA.Proofs.TR04.exists_legalTrace P start
example {P : Program} {start : State P} {trace : Trace P}
    (h : LegalTrace P start trace) (t : ℕ) : trace.cost t = charge P (trace.state t) :=
  NLA.Proofs.TR04.legalTrace_cost_eq h t
end
