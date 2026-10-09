import NLA.Computation.ExactRealMachine
import NLA.Statements.IE12

/-! Kernel-checked operational controls for the IE-12 model. These small traces
check addressing, instruction costs, stream separation and failure behavior.
No program here is claimed to solve the catalog problem. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Computation.ExactRealMachine.Controls

private abbrev matrix2 : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => 10 * (i.val : ℝ) + j.val + 1

private abbrev rhs2 : Fin 2 → ℝ := fun i => 20 + i.val

/-- Dense matrix, RHS, tolerance and zero default occupy disjoint exact cells. -/
theorem input_layout :
    inputMemory matrix2 rhs2 (1 / 4) 0 = 1 ∧
    inputMemory matrix2 rhs2 (1 / 4) 1 = 2 ∧
    inputMemory matrix2 rhs2 (1 / 4) 2 = 11 ∧
    inputMemory matrix2 rhs2 (1 / 4) 3 = 12 ∧
    inputMemory matrix2 rhs2 (1 / 4) 4 = 20 ∧
    inputMemory matrix2 rhs2 (1 / 4) 5 = 21 ∧
    inputMemory matrix2 rhs2 (1 / 4) 6 = 1 / 4 ∧
    inputMemory matrix2 rhs2 (1 / 4) 7 = 0 := by
  classical
  norm_num [inputMemory, matrix2, rhs2]

private abbrev returnRhs2 : Program where
  extraLabels := 1
  realRegisters := 0
  extraNatRegisters := 0
  constantCount := 0
  constants := Fin.elim0
  code := fun label => if label = 0 then .natural 0 4 1 else .halt 0

/-- Setting the output address does not halt; the second instruction does. -/
theorem halt_is_charged (omega : Streams) :
    output returnRhs2 2 (run returnRhs2 matrix2 rhs2 (1 / 4) omega 1) = none ∧
    output returnRhs2 2 (run returnRhs2 matrix2 rhs2 (1 / 4) omega 2) = some rhs2 := by
  classical
  constructor
  · simp [output, run, step, initial, returnRhs2]
  · simp [output, run, step, initial, returnRhs2]
    funext i
    fin_cases i <;> norm_num [inputMemory, rhs2]

private abbrev divideZero : Program where
  extraLabels := 0
  realRegisters := 1
  extraNatRegisters := 0
  constantCount := 0
  constants := Fin.elim0
  code := fun _ => .divReal 0 0 0 0

/-- Totalized field division must not make a zero-denominator instruction succeed. -/
theorem division_failure (omega : Streams) :
    (run divideZero matrix2 rhs2 (1 / 4) omega 1).status = .failed ∧
    output divideZero 2 (run divideZero matrix2 rhs2 (1 / 4) omega 1) = none := by
  classical
  simp [run, step, initial, divideZero, output]

private abbrev rootNegative : Program where
  extraLabels := 0
  realRegisters := 1
  extraNatRegisters := 0
  constantCount := 0
  constants := Fin.elim0
  code := fun _ => .sqrtReal 0 0 0

/-- Real.sqrt's total value on a negative input cannot mask machine failure. -/
theorem root_failure (omega : Streams) :
    (step rootNegative omega
      { initial rootNegative matrix2 rhs2 (1 / 4) with real := fun _ => -1 }).status = .failed := by
  classical
  norm_num [step, initial, rootNegative]

theorem failed_absorbing (P : Program) (omega : Streams) (s : State P)
    (h : s.status = .failed) : step P omega s = s := by
  classical
  simp [step, h]

theorem halted_absorbing (P : Program) (omega : Streams) (s : State P) (a : ℕ)
    (h : s.status = .halted a) : step P omega s = s := by
  classical
  simp [step, h]

private abbrev draws : Program where
  extraLabels := 3
  realRegisters := 3
  extraNatRegisters := 0
  constantCount := 0
  constants := Fin.elim0
  code := fun label =>
    if label = 0 then .gaussian 0 1
    else if label = 1 then .bit 1 2
    else if label = 2 then .gaussian 2 3
    else .halt 0

/-- Adaptive instruction types use separate sequential coordinates: G0,B0,G1. -/
theorem separate_stream_cursors (omega : Streams) :
    let s := run draws matrix2 rhs2 (1 / 4) omega 3
    s.real 0 = omega.1 0 ∧ s.real 1 = (if omega.2 0 then 1 else 0) ∧
    s.real 2 = omega.1 1 ∧ s.gaussianCursor = 2 ∧ s.bitCursor = 1 := by
  classical
  simp [run, step, initial, draws, Function.update]

theorem streams_probability : MeasureTheory.IsProbabilityMeasure StreamLaw := inferInstance

#assert_trust kernel input_layout
#assert_trust kernel halt_is_charged
#assert_trust kernel division_failure
#assert_trust kernel root_failure
#assert_trust kernel failed_absorbing
#assert_trust kernel halted_absorbing
#assert_trust kernel separate_stream_cursors
#assert_trust kernel streams_probability

end NLA.Computation.ExactRealMachine.Controls
