import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.ProductMeasure
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

/-! A concrete finite exact-real indexed RAM for IE-12. Every running transition
executes one scalar instruction. Neither a solver, its cost nor its result is
a parameter of the evaluator. This model makes no algorithmic existence claim. -/
set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace NLA.Computation.ExactRealMachine

/-- Every register, literal and successor is a finite piece of program syntax.
Natural literals are fixed with the program. There is no real-to-natural operation. -/
inductive Instruction (labels reals naturals constants : ℕ) where
  | constant (dst : Fin reals) (value : Fin constants) (next : Fin labels)
  | copyReal (dst src : Fin reals) (next : Fin labels)
  | addReal (dst left right : Fin reals) (next : Fin labels)
  | subReal (dst left right : Fin reals) (next : Fin labels)
  | mulReal (dst left right : Fin reals) (next : Fin labels)
  | divReal (dst left right : Fin reals) (next : Fin labels)
  | sqrtReal (dst src : Fin reals) (next : Fin labels)
  | lessReal (left right : Fin reals) (yes no : Fin labels)
  | equalReal (left right : Fin reals) (yes no : Fin labels)
  | natural (dst : Fin naturals) (value : ℕ) (next : Fin labels)
  | copyNat (dst src : Fin naturals) (next : Fin labels)
  | increment (dst : Fin naturals) (next : Fin labels)
  | decrement (dst : Fin naturals) (next : Fin labels)
  | addNat (dst left right : Fin naturals) (next : Fin labels)
  | mulNat (dst left right : Fin naturals) (next : Fin labels)
  | lessNat (left right : Fin naturals) (yes no : Fin labels)
  | equalNat (left right : Fin naturals) (yes no : Fin labels)
  | castNat (dst : Fin reals) (src : Fin naturals) (next : Fin labels)
  | read (dst : Fin reals) (address : Fin naturals) (next : Fin labels)
  | write (address : Fin naturals) (src : Fin reals) (next : Fin labels)
  | gaussian (dst : Fin reals) (next : Fin labels)
  | bit (dst : Fin reals) (next : Fin labels)
  | jump (next : Fin labels)
  | halt (address : Fin naturals)

/-- `extraLabels+1` and `extraNatRegisters+1` ensure the initial label and
input-size register exist. The constant pool and scratch-register count may be zero. -/
structure Program where
  extraLabels : ℕ
  realRegisters : ℕ
  extraNatRegisters : ℕ
  constantCount : ℕ
  constants : Fin constantCount → ℝ
  code : Fin (extraLabels + 1) →
    Instruction (extraLabels + 1) realRegisters (extraNatRegisters + 1) constantCount

/-- A successful halt records an ordinary memory address, not an output oracle. -/
inductive Status where
  | running
  | halted (address : ℕ)
  | failed
  deriving DecidableEq

structure State (P : Program) where
  label : Fin (P.extraLabels + 1)
  real : Fin P.realRegisters → ℝ
  natural : Fin (P.extraNatRegisters + 1) → ℕ
  memory : ℕ → ℝ
  gaussianCursor : ℕ
  bitCursor : ℕ
  status : Status

abbrev Streams := (ℕ → ℝ) × (ℕ → Bool)

/-- The actual fair Boolean law: half the mass at true and half at false. -/
noncomputable def FairBitLaw : Measure Bool :=
  bernoulliMeasure true false ⟨(1 / 2 : ℝ), by norm_num⟩

instance : IsProbabilityMeasure FairBitLaw := by
  unfold FairBitLaw
  infer_instance

/-- Countably many independent standard Gaussians, countably many independent
fair bits, and independence between the two streams. -/
noncomputable def StreamLaw : Measure Streams :=
  (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)).prod
    (Measure.infinitePi (fun _ : ℕ => FairBitLaw))

instance : IsProbabilityMeasure StreamLaw := by
  unfold StreamLaw
  infer_instance

/-- Exact dense input layout; all noninput locations start at zero. The
quotient/remainder calculations here describe free input placement, not RAM opcodes. -/
def inputMemory {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (epsilon : ℝ) (address : ℕ) : ℝ :=
  if hA : address < n * n then
    have hn : 0 < n := by
      by_contra h
      have : n = 0 := by omega
      simp_all
    A ⟨address / n, (Nat.div_lt_iff_lt_mul hn).mpr hA⟩
      ⟨address % n, Nat.mod_lt address hn⟩
  else if hb : address - n * n < n then
    b ⟨address - n * n, hb⟩
  else if address = n * n + n then epsilon else 0

def initial (P : Program) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (epsilon : ℝ) : State P where
  label := 0
  real := fun _ => 0
  natural := fun r => if r = 0 then n else 0
  memory := inputMemory A b epsilon
  gaussianCursor := 0
  bitCursor := 0
  status := .running

/-- One charged transition. Every operand is read from the old state before
its destination is updated. Illegal division/root operations fail, never halt. -/
noncomputable def step (P : Program) (omega : Streams) (s : State P) : State P := by
  classical
  exact match s.status with
  | .halted _ => s
  | .failed => s
  | .running => match P.code s.label with
    | .constant dst value next =>
        { s with label := next, real := Function.update s.real dst (P.constants value) }
    | .copyReal dst src next =>
        { s with label := next, real := Function.update s.real dst (s.real src) }
    | .addReal dst left right next =>
        { s with label := next, real := Function.update s.real dst (s.real left + s.real right) }
    | .subReal dst left right next =>
        { s with label := next, real := Function.update s.real dst (s.real left - s.real right) }
    | .mulReal dst left right next =>
        { s with label := next, real := Function.update s.real dst (s.real left * s.real right) }
    | .divReal dst left right next =>
        if s.real right = 0 then { s with status := .failed }
        else { s with label := next, real := Function.update s.real dst (s.real left / s.real right) }
    | .sqrtReal dst src next =>
        if s.real src < 0 then { s with status := .failed }
        else { s with label := next, real := Function.update s.real dst (Real.sqrt (s.real src)) }
    | .lessReal left right yes no =>
        { s with label := if s.real left < s.real right then yes else no }
    | .equalReal left right yes no =>
        { s with label := if s.real left = s.real right then yes else no }
    | .natural dst value next =>
        { s with label := next, natural := Function.update s.natural dst value }
    | .copyNat dst src next =>
        { s with label := next, natural := Function.update s.natural dst (s.natural src) }
    | .increment dst next =>
        { s with label := next, natural := Function.update s.natural dst (s.natural dst + 1) }
    | .decrement dst next =>
        { s with label := next, natural := Function.update s.natural dst (s.natural dst - 1) }
    | .addNat dst left right next =>
        { s with label := next, natural := Function.update s.natural dst (s.natural left + s.natural right) }
    | .mulNat dst left right next =>
        { s with label := next, natural := Function.update s.natural dst (s.natural left * s.natural right) }
    | .lessNat left right yes no =>
        { s with label := if s.natural left < s.natural right then yes else no }
    | .equalNat left right yes no =>
        { s with label := if s.natural left = s.natural right then yes else no }
    | .castNat dst src next =>
        { s with label := next, real := Function.update s.real dst (s.natural src : ℝ) }
    | .read dst address next =>
        { s with label := next, real := Function.update s.real dst (s.memory (s.natural address)) }
    | .write address src next =>
        { s with label := next, memory := Function.update s.memory (s.natural address) (s.real src) }
    | .gaussian dst next =>
        { s with
            label := next
            real := Function.update s.real dst (omega.1 s.gaussianCursor)
            gaussianCursor := s.gaussianCursor + 1 }
    | .bit dst next =>
        { s with
            label := next
            real := Function.update s.real dst (if omega.2 s.bitCursor then 1 else 0)
            bitCursor := s.bitCursor + 1 }
    | .jump next => { s with label := next }
    | .halt address => { s with status := .halted (s.natural address) }

/-- Natural iteration; t counts instructions including the successful halt.
Absorbing states permit a later witness without changing any returned value. -/
noncomputable def run (P : Program) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (epsilon : ℝ) (omega : Streams) : ℕ → State P
  | 0 => initial P A b epsilon
  | t + 1 => step P omega (run P A b epsilon omega t)

/-- Only the successful tag returns a vector. Its length is the original input
dimension, even if a program overwrites its initial size register. -/
def output (P : Program) (n : ℕ) (s : State P) : Option (Fin n → ℝ) :=
  match s.status with
  | .halted address => some (fun i => s.memory (address + i.val))
  | .running => none
  | .failed => none

end NLA.Computation.ExactRealMachine
