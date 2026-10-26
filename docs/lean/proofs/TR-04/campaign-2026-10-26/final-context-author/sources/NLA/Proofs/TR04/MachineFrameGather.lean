import NLA.Proofs.TR04.MachineFrameGatherMemory
import NLA.Proofs.TR04.MachineNoEarlyHalt
import Mathlib.Tactic.FinCases

/-! One fixed literal RAM program materializes selected columns of a full
square matrix. Its only cyclic operations are increment, equality and reset. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

/-- Naturals: row,m,h,t,s,j,source,output,width,column,cyclic,rowBase,
selected,readAddress,writeAddress. Real zero is the read/write scratch. -/
def frameGatherProgram : Program where
  extraLabels := 25
  realRegisters := 1
  extraNatRegisters := 14
  constantCount := 0
  constants := Fin.elim0
  code label := match label.val with
    | 0 => .natural 0 0 1
    | 1 => .copyNat 14 7 2
    | 2 => .addNat 8 2 4 3
    | 3 => .lessNat 0 1 4 25
    | 4 => .natural 9 0 5
    | 5 => .copyNat 10 5 6
    | 6 => .mulNat 11 0 1 7
    | 7 => .addNat 11 6 11 8
    | 8 => .lessNat 9 8 9 24
    | 9 => .lessNat 9 2 10 14
    | 10 => .copyNat 12 9 11
    | 11 => .jump 12
    | 12 => .jump 13
    | 13 => .jump 19
    | 14 => .addNat 12 2 10 15
    | 15 => .increment 10 16
    | 16 => .equalNat 10 3 17 18
    | 17 => .natural 10 0 19
    | 18 => .jump 19
    | 19 => .addNat 13 11 12 20
    | 20 => .read 0 13 21
    | 21 => .write 14 0 22
    | 22 => .increment 14 23
    | 23 => .increment 9 8
    | 24 => .increment 0 3
    | _ => .halt 7

def frameGatherOuterState (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (i : ℕ) (aux : Fin 5 → ℕ) (value : ℝ) : State frameGatherProgram where
  label := 3
  real := fun _ => value
  natural := ![i, P.rows, P.above, P.tied, P.take, P.start, P.inputBase, P.outputBase,
    P.width, aux 0, aux 1, aux 2, aux 3, aux 4, P.outputBase + i * P.width]
  memory := frameGatherMemory memory P (i * P.width)
  status := .running

def frameGatherStart (memory : ℕ → ℝ) (P : FrameGatherParameters) (aux : Fin 5 → ℕ)
    (rowScratch widthScratch writeScratch : ℕ) (value : ℝ) : State frameGatherProgram :=
  { frameGatherOuterState memory P 0 aux value with
    label := 0
    natural := ![rowScratch, P.rows, P.above, P.tied, P.take, P.start, P.inputBase, P.outputBase,
      widthScratch, aux 0, aux 1, aux 2, aux 3, aux 4, writeScratch]
    memory := memory }

def frameGatherInnerState (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (i k selected address : ℕ) (value : ℝ) : State frameGatherProgram where
  label := 8
  real := fun _ => value
  natural := ![i, P.rows, P.above, P.tied, P.take, P.start, P.inputBase, P.outputBase,
    P.width, k, P.counter k, P.inputBase + i * P.rows, selected, address,
    P.outputBase + (i * P.width + k)]
  memory := frameGatherMemory memory P (i * P.width + k)
  status := .running

theorem frameGatherProgram_scalar (s : State frameGatherProgram) :
    instructionIsSVD (frameGatherProgram.code s.label) = false := by
  rcases s with ⟨label, reals, naturals, memory, status⟩
  fin_cases label <;> rfl

set_option maxHeartbeats 1200000 in
theorem frameGatherProgram_initialize (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (aux : Fin 5 → ℕ) (rowScratch widthScratch writeScratch : ℕ) (value : ℝ) :
    (ordinaryStep frameGatherProgram)^[3]
      (frameGatherStart memory P aux rowScratch widthScratch writeScratch value) =
        frameGatherOuterState memory P 0 aux value := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
    frameGatherProgram, frameGatherStart, frameGatherOuterState,
    FrameGatherParameters.width, frameGatherMemory_zero]
  all_goals try rfl
  funext k
  fin_cases k <;> simp [Function.update, Fin.ext_iff]

set_option maxHeartbeats 1200000 in
theorem frameGatherProgram_row_setup (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (hP : P.Valid) (i : ℕ) (hi : i < P.rows) (aux : Fin 5 → ℕ) (value : ℝ) :
    (ordinaryStep frameGatherProgram)^[5] (frameGatherOuterState memory P i aux value) =
      frameGatherInnerState memory P i 0 (aux 3) (aux 4) value := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
    frameGatherProgram, frameGatherOuterState, frameGatherInnerState, hi,
    P.counter_prefix hP 0 (Nat.zero_le _)]
  all_goals try rfl
  funext k
  fin_cases k <;> simp [Function.update, Fin.ext_iff]

#assert_trust kernel frameGatherProgram
#assert_trust kernel frameGatherProgram_scalar
#assert_trust kernel frameGatherProgram_initialize
#assert_trust kernel frameGatherProgram_row_setup
#print axioms frameGatherProgram_row_setup
end NLA.Proofs.TR04
