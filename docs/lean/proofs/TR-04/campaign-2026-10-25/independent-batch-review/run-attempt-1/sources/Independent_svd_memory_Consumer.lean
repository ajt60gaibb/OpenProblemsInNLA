import NLA.Proofs.TR04.MachineSVDMemory

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
#assert_kind NLA.Proofs.TR04.matrix_offset_lt "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrix_offset_lt
#print axioms NLA.Proofs.TR04.matrix_offset_lt
#assert_kind NLA.Proofs.TR04.matrixCell_entry "theorem"
#assert_trust kernel NLA.Proofs.TR04.matrixCell_entry
#print axioms NLA.Proofs.TR04.matrixCell_entry
#assert_kind NLA.Proofs.TR04.disjointBlocks_not_mem_right "theorem"
#assert_trust kernel NLA.Proofs.TR04.disjointBlocks_not_mem_right
#print axioms NLA.Proofs.TR04.disjointBlocks_not_mem_right
#assert_kind NLA.Proofs.TR04.disjointBlocks_not_mem_left "theorem"
#assert_trust kernel NLA.Proofs.TR04.disjointBlocks_not_mem_left
#print axioms NLA.Proofs.TR04.disjointBlocks_not_mem_left
#assert_kind NLA.Proofs.TR04.writeSVD_u_entry "theorem"
#assert_trust kernel NLA.Proofs.TR04.writeSVD_u_entry
#print axioms NLA.Proofs.TR04.writeSVD_u_entry
#assert_kind NLA.Proofs.TR04.readMatrix_writeSVD_u "theorem"
#assert_trust kernel NLA.Proofs.TR04.readMatrix_writeSVD_u
#print axioms NLA.Proofs.TR04.readMatrix_writeSVD_u
#assert_kind NLA.Proofs.TR04.writeSVD_sigma_entry "theorem"
#assert_trust kernel NLA.Proofs.TR04.writeSVD_sigma_entry
#print axioms NLA.Proofs.TR04.writeSVD_sigma_entry
#assert_kind NLA.Proofs.TR04.writeSVD_v_entry "theorem"
#assert_trust kernel NLA.Proofs.TR04.writeSVD_v_entry
#print axioms NLA.Proofs.TR04.writeSVD_v_entry
#assert_kind NLA.Proofs.TR04.readMatrix_writeSVD_v "theorem"
#assert_trust kernel NLA.Proofs.TR04.readMatrix_writeSVD_v
#print axioms NLA.Proofs.TR04.readMatrix_writeSVD_v
#assert_kind NLA.Proofs.TR04.writeSVD_outside "theorem"
#assert_trust kernel NLA.Proofs.TR04.writeSVD_outside
#print axioms NLA.Proofs.TR04.writeSVD_outside

noncomputable section
open scoped BigOperators Matrix InnerProductSpace
open NLA.Computation.SVDMachine
namespace NLA.Proofs.TR04
example {m l : ℕ} (A : Matrix (Fin m) (Fin l) ℝ)
    (i : Fin m) (j : Fin l) : matrixCell A (i.val * l + j.val) = A i j := @NLA.Proofs.TR04.matrixCell_entry m l A i j
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
example {m l : ℕ} (memory : ℕ → ℝ)
    (uBase sigmaBase vBase : ℕ) (U : Matrix (Fin m) (Fin m) ℝ)
    (sigma : Fin (min m l) → ℝ) (V : Matrix (Fin l) (Fin l) ℝ) :
    readMatrix (writeSVD memory uBase sigmaBase vBase U sigma V) m m uBase = U := @NLA.Proofs.TR04.readMatrix_writeSVD_u m l memory uBase sigmaBase vBase U sigma V
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
example {m l : ℕ} (memory : ℕ → ℝ)
    (uBase sigmaBase vBase : ℕ) (U : Matrix (Fin m) (Fin m) ℝ)
    (sigma : Fin (min m l) → ℝ) (V : Matrix (Fin l) (Fin l) ℝ)
    (h : OutputBlocksDisjoint m l uBase sigmaBase vBase) (k : Fin (min m l)) :
    writeSVD memory uBase sigmaBase vBase U sigma V (sigmaBase + k.val) = sigma k := @NLA.Proofs.TR04.writeSVD_sigma_entry m l memory uBase sigmaBase vBase U sigma V h k
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
example {m l : ℕ} (memory : ℕ → ℝ)
    (uBase sigmaBase vBase : ℕ) (U : Matrix (Fin m) (Fin m) ℝ)
    (sigma : Fin (min m l) → ℝ) (V : Matrix (Fin l) (Fin l) ℝ)
    (h : OutputBlocksDisjoint m l uBase sigmaBase vBase) :
    readMatrix (writeSVD memory uBase sigmaBase vBase U sigma V) l l vBase = V := @NLA.Proofs.TR04.readMatrix_writeSVD_v m l memory uBase sigmaBase vBase U sigma V h
end NLA.Proofs.TR04
namespace NLA.Proofs.TR04
example {m l : ℕ} (memory : ℕ → ℝ)
    (uBase sigmaBase vBase : ℕ) (U : Matrix (Fin m) (Fin m) ℝ)
    (sigma : Fin (min m l) → ℝ) (V : Matrix (Fin l) (Fin l) ℝ) (address : ℕ)
    (hu : ¬ (uBase ≤ address ∧ address < uBase + m * m))
    (hs : ¬ (sigmaBase ≤ address ∧ address < sigmaBase + min m l))
    (hv : ¬ (vBase ≤ address ∧ address < vBase + l * l)) :
    writeSVD memory uBase sigmaBase vBase U sigma V address = memory address := @NLA.Proofs.TR04.writeSVD_outside m l memory uBase sigmaBase vBase U sigma V address hu hs hv
end NLA.Proofs.TR04
end
