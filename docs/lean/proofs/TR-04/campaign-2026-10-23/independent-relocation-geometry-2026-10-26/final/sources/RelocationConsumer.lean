import NLA.Proofs.TR04.MachineSVDRelocation
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace IndependentRelocationGeometry
open NLA.Computation.SVDMachine NLA.Proofs.TR04

/-- Local copy labels map to [4,7,1,6,2,8,3], its natural registers to
[6,2,7,1,5], and its real scratch to register2. Label3 has actual caller
continuation code, rather than the local halt. -/
def copyCaller : Program where
  extraLabels := 8
  realRegisters := 3
  extraNatRegisters := 7
  constantCount := 0
  constants := Fin.elim0
  code label := match label.val with
    | 1 => .write 1 2 6
    | 2 => .increment 1 8
    | 3 => .natural 0 999 0
    | 4 => .lessNat 6 2 7 3
    | 6 => .increment 7 2
    | 7 => .read 2 7 1
    | 8 => .increment 6 4
    | _ => .halt 0

def copyLabels (i : Fin 7) : Fin 9 := match i.val with
  | 0 => 4 | 1 => 7 | 2 => 1 | 3 => 6 | 4 => 2 | 5 => 8 | _ => 3
def copyNaturals (i : Fin 5) : Fin 8 := match i.val with
  | 0 => 6 | 1 => 2 | 2 => 7 | 3 => 1 | _ => 5

def outsideReal : Fin copyCaller.realRegisters := ⟨0, by change 0 < 3; omega⟩

def copyEmbedding : RoutineEmbedding copyProgram copyCaller where
  labels := copyLabels
  reals := fun _ => ⟨2, by change 2 < 3; omega⟩
  naturals := copyNaturals
  constants := Fin.elim0
  reals_injective := by
    intro i j _
    apply Fin.ext
    have hi : i.val < 1 := i.isLt
    have hj : j.val < 1 := j.isLt
    omega
  naturals_injective := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
        -Fin.val_eq_zero_iff, Fin.ext_iff, copyNaturals] at h ⊢
  constant_values := by intro i; exact Fin.elim0 i
  code := by
    intro l hl
    fin_cases l <;> first | rfl | cases hl

def copyCallerStart (old : ℕ → ℝ) (src dst count : ℕ) (scratch r0 r1 : ℝ)
    (n0 n3 n4 : ℕ) : State copyCaller where
  label := 4
  real := ![r0, r1, scratch]
  natural := ![n0, dst, count, n3, n4, dst, 0, src]
  memory := old
  status := .running

theorem concrete_copy_related (old : ℕ → ℝ) (src dst count : ℕ) (scratch r0 r1 : ℝ)
    (n0 n3 n4 : ℕ) : copyEmbedding.Relates (copyLoopState old src dst count 0 scratch)
      (copyCallerStart old src dst count scratch r0 r1 n0 n3 n4) := by
  constructor
  · rfl
  · funext i
    fin_cases i
    rfl
  · funext i
    fin_cases i <;> rfl
  · simp [copyCallerStart, copyLoopState, copiedMemory_zero]
  · rfl

theorem concrete_copy_trace_exists (old : ℕ → ℝ) (src dst count : ℕ)
    (scratch r0 r1 : ℝ) (n0 n3 n4 : ℕ) :
    ∃ trace, LegalTrace copyCaller
      (copyCallerStart old src dst count scratch r0 r1 n0 n3 n4) trace :=
  exists_legalTrace _ _

theorem concrete_copy_any_caller_time (old : ℕ → ℝ) (src dst count : ℕ)
    (scratch : ℝ) (hd : DisjointBlocks src count dst count)
    {start : State copyCaller} {trace : Trace copyCaller} (ht : LegalTrace copyCaller start trace)
    (offset : ℕ)
    (hs : copyEmbedding.Relates (copyLoopState old src dst count 0 scratch) (trace.state offset)) :
    (trace.state (offset + (6 * count + 1))).label = 3 ∧
    (trace.state (offset + (6 * count + 1))).status = .running ∧
    (∀ i < count, (trace.state (offset + (6 * count + 1))).memory (dst + i) = old (src + i)) ∧
    (∀ address, ¬ (dst ≤ address ∧ address < dst + count) →
      (trace.state (offset + (6 * count + 1))).memory address = old address) ∧
    CostThrough copyCaller trace (offset + (6 * count + 1)) ≤
      CostThrough copyCaller trace offset + (6 * count + 1) ∧
    (trace.state (offset + (6 * count + 1))).real outsideReal =
      (trace.state offset).real outsideReal ∧
    (trace.state (offset + (6 * count + 1))).natural 0 = (trace.state offset).natural 0 := by
  obtain ⟨value, hr, hc⟩ := copyEmbedding.copy_run_at old src dst count scratch hd ht offset hs
  have hno := copyProgram_nohalt_prefix old src dst count scratch hd
  have hscalar : ∀ k < 6 * count + 1,
      instructionIsSVD (copyProgram.code
        ((ordinaryStep copyProgram)^[k] (copyLoopState old src dst count 0 scratch)).label) =
        false := fun _ _ => copyProgram_scalar _
  have hreal := copyEmbedding.scalar_trace_real_outside _ hs (legalTrace_shift ht offset)
    _ hno hscalar outsideReal (by intro i; fin_cases i; decide)
  have hnatural := copyEmbedding.scalar_trace_natural_outside _ hs (legalTrace_shift ht offset)
    _ hno hscalar 0 (by intro i; fin_cases i <;> decide)
  refine ⟨hr.label, hr.status, ?_, ?_, hc, hreal, hnatural⟩
  · intro i hi
    rw [hr.memory]
    simp [copyReturnState, copyLoopState, copiedMemory, hi]
  · intro address ha
    rw [hr.memory]
    exact copiedMemory_outside old src dst count address ha

/-- A second concrete embedding tests a rectangular SVD instruction, a
nonidentity label/register permutation, and a nonempty constant pool map. -/
def localSVD : Program where
  extraLabels := 1
  realRegisters := 1
  extraNatRegisters := 6
  constantCount := 1
  constants := fun _ => 7
  code label := match label.val with
    | 0 => .svd 0 1 2 3 4 5 1
    | _ => .halt 6

def svdCaller : Program where
  extraLabels := 2
  realRegisters := 3
  extraNatRegisters := 8
  constantCount := 2
  constants := ![2, 7]
  code label := match label.val with
    | 2 => .svd 8 4 2 7 1 6 0
    | 0 => .increment 0 1
    | _ => .halt 0

def svdLabels (i : Fin 2) : Fin 3 := match i.val with | 0 => 2 | _ => 0
def svdNaturals (i : Fin 7) : Fin 9 := match i.val with
  | 0 => 8 | 1 => 4 | 2 => 2 | 3 => 7 | 4 => 1 | 5 => 6 | _ => 5

def svdEmbedding : RoutineEmbedding localSVD svdCaller where
  labels := svdLabels
  reals := fun _ => ⟨2, by change 2 < 3; omega⟩
  naturals := svdNaturals
  constants := fun _ => ⟨1, by change 1 < 2; omega⟩
  reals_injective := by
    intro i j _
    apply Fin.ext
    have hi : i.val < 1 := i.isLt
    have hj : j.val < 1 := j.isLt
    omega
  naturals_injective := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
        -Fin.val_eq_zero_iff, Fin.ext_iff, svdNaturals] at h ⊢
  constant_values := by intro i; rfl
  code := by intro l hl; fin_cases l <;> first | rfl | cases hl

theorem every_actual_rectangular_SVD_reply {s : State localSVD} (hs : s.status = .running)
    (hl : s.label = 0) {start : State svdCaller} {trace : Trace svdCaller}
    (ht : LegalTrace svdCaller start trace) (time : ℕ)
    (h : svdEmbedding.Relates s (trace.state time))
    (hd : OutputBlocksDisjoint (s.natural 0) (s.natural 1)
      (s.natural 3) (s.natural 4) (s.natural 5)) :
    ∃ U : Matrix (Fin (s.natural 0)) (Fin (s.natural 0)) ℝ,
    ∃ sigma : Fin (min (s.natural 0) (s.natural 1)) → ℝ,
    ∃ V : Matrix (Fin (s.natural 1)) (Fin (s.natural 1)) ℝ,
      ValidSVD (readMatrix s.memory (s.natural 0) (s.natural 1) (s.natural 2)) U sigma V ∧
      svdEmbedding.Relates
        { s with
          label := 1
          memory := writeSVD s.memory (s.natural 3) (s.natural 4) (s.natural 5) U sigma V }
        (trace.state (time + 1)) ∧
      trace.cost time = (s.natural 0 + s.natural 1 + 1)^3 := by
  exact svdEmbedding.svd_trace_step ht time h hs 0 1 2 3 4 5 1
    (by rw [hl]; rfl) hd

#assert_trust kernel copyEmbedding
#assert_trust kernel concrete_copy_related
#assert_trust kernel concrete_copy_trace_exists
#assert_trust kernel concrete_copy_any_caller_time
#assert_trust kernel svdEmbedding
#assert_trust kernel every_actual_rectangular_SVD_reply
#print axioms copyEmbedding
#print axioms concrete_copy_related
#print axioms concrete_copy_trace_exists
#print axioms concrete_copy_any_caller_time
#print axioms svdEmbedding
#print axioms every_actual_rectangular_SVD_reply
end IndependentRelocationGeometry
#assert_trust kernel NLA.Proofs.TR04.instructionIsHalt
#print axioms NLA.Proofs.TR04.instructionIsHalt
#assert_trust kernel NLA.Proofs.TR04.relocateInstruction
#print axioms NLA.Proofs.TR04.relocateInstruction
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding
#print axioms NLA.Proofs.TR04.RoutineEmbedding
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.Relates
#print axioms NLA.Proofs.TR04.RoutineEmbedding.Relates
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.Relates.real_apply
#print axioms NLA.Proofs.TR04.RoutineEmbedding.Relates.real_apply
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.Relates.natural_apply
#print axioms NLA.Proofs.TR04.RoutineEmbedding.Relates.natural_apply
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.ordinaryStep_relates
#print axioms NLA.Proofs.TR04.RoutineEmbedding.ordinaryStep_relates
#assert_trust kernel NLA.Proofs.TR04.instructionIsSVD_relocate
#print axioms NLA.Proofs.TR04.instructionIsSVD_relocate
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.charge_eq
#print axioms NLA.Proofs.TR04.RoutineEmbedding.charge_eq
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.scalar_step
#print axioms NLA.Proofs.TR04.RoutineEmbedding.scalar_step
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_prefix
#print axioms NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_prefix
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_cost
#print axioms NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_cost
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_cost_le
#print axioms NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_cost_le
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.ordinaryStep_real_outside
#print axioms NLA.Proofs.TR04.RoutineEmbedding.ordinaryStep_real_outside
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.ordinaryStep_natural_outside
#print axioms NLA.Proofs.TR04.RoutineEmbedding.ordinaryStep_natural_outside
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_real_outside
#print axioms NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_real_outside
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_natural_outside
#print axioms NLA.Proofs.TR04.RoutineEmbedding.scalar_trace_natural_outside
#assert_trust kernel NLA.Proofs.TR04.copyProgram_nohalt_phase
#print axioms NLA.Proofs.TR04.copyProgram_nohalt_phase
#assert_trust kernel NLA.Proofs.TR04.copyProgram_nohalt_prefix
#print axioms NLA.Proofs.TR04.copyProgram_nohalt_prefix
#assert_trust kernel NLA.Proofs.TR04.copyReturnState
#print axioms NLA.Proofs.TR04.copyReturnState
#assert_trust kernel NLA.Proofs.TR04.copyProgram_return
#print axioms NLA.Proofs.TR04.copyProgram_return
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.copy_run
#print axioms NLA.Proofs.TR04.RoutineEmbedding.copy_run
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalProgram_nohalt_phase
#print axioms NLA.Proofs.TR04.decodeNaturalProgram_nohalt_phase
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalProgram_nohalt_initial
#print axioms NLA.Proofs.TR04.decodeNaturalProgram_nohalt_initial
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalProgram_nohalt_prefix
#print axioms NLA.Proofs.TR04.decodeNaturalProgram_nohalt_prefix
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalReturnState
#print axioms NLA.Proofs.TR04.decodeNaturalReturnState
#assert_trust kernel NLA.Proofs.TR04.decodeNaturalProgram_return
#print axioms NLA.Proofs.TR04.decodeNaturalProgram_return
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.decodeNatural_run
#print axioms NLA.Proofs.TR04.RoutineEmbedding.decodeNatural_run
#assert_trust kernel NLA.Proofs.TR04.shiftedTrace
#print axioms NLA.Proofs.TR04.shiftedTrace
#assert_trust kernel NLA.Proofs.TR04.legalTrace_shift
#print axioms NLA.Proofs.TR04.legalTrace_shift
#assert_trust kernel NLA.Proofs.TR04.costThrough_shift
#print axioms NLA.Proofs.TR04.costThrough_shift
#assert_trust kernel NLA.Proofs.TR04.costThrough_compose_le
#print axioms NLA.Proofs.TR04.costThrough_compose_le
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.copy_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.copy_run_at
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.decodeNatural_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.decodeNatural_run_at
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.svd_step
#print axioms NLA.Proofs.TR04.RoutineEmbedding.svd_step
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.svd_trace_step
#print axioms NLA.Proofs.TR04.RoutineEmbedding.svd_trace_step
