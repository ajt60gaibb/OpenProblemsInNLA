import Mathlib

/-! A finite-code rounded floating-point machine for Schur statement
boundaries. The program cannot inspect a mathematical matrix except through
the `input` instruction, which rounds one real component at its fixed
mantissa precision. Every random choice reads one bit from a finite tape.
There are no exact-real arithmetic, Gaussian, eigensolver or SVD instructions. -/
set_option autoImplicit false
open Classical
open scoped BigOperators

namespace NLA.Computation.FiniteFloatMachine

/-- A signed binary significand and a binary exponent. The exponent only
sets scale; all significant bits are in the integer significand. -/
structure Float where
  mantissa : ℤ
  exponent : ℤ
  deriving DecidableEq

def zero : Float := ⟨0, 0⟩

noncomputable def value (x : Float) : ℝ :=
  (x.mantissa : ℝ) * (2 : ℝ) ^ x.exponent

/-- One fixed round-to-nearest rule, with half ties rounded upward. The
carry step renormalizes a significand that rounds to `2^precision`.
All exact logarithms and floors here specify the hardware operation's
semantics; neither is an instruction available to the program. -/
noncomputable def round (precision : ℕ) (x : ℝ) : Float :=
  if x = 0 then zero else
    let exponent := Int.floor (Real.log |x| / Real.log 2) - (precision : ℤ) + 1
    let significand := Int.floor (x / (2 : ℝ) ^ exponent + 1 / 2)
    if (2 : ℤ) ^ precision ≤ (significand.natAbs : ℤ) then
      ⟨significand / 2, exponent + 1⟩
    else ⟨significand, exponent⟩

def MantissaFits (precision : ℕ) (x : Float) : Prop :=
  x.mantissa.natAbs < 2 ^ precision

/-- Fixed finite instruction syntax. Natural-number operations implement
indexes, loops and precision selection. Real arithmetic is possible only
on stored rounded floats and rounds every result back to the selected
precision. All literal constants are rational and fixed with the code. -/
inductive Instruction (labels reals naturals constants : ℕ) where
  | constant (dst : Fin reals) (literal : Fin constants) (next : Fin labels)
  | copyReal (dst src : Fin reals) (next : Fin labels)
  | addReal (dst left right : Fin reals) (next : Fin labels)
  | subReal (dst left right : Fin reals) (next : Fin labels)
  | mulReal (dst left right : Fin reals) (next : Fin labels)
  | divReal (dst left right : Fin reals) (next : Fin labels)
  | sqrtReal (dst src : Fin reals) (next : Fin labels)
  | lessReal (left right : Fin reals) (yes no : Fin labels)
  | equalReal (left right : Fin reals) (yes no : Fin labels)
  | natural (dst : Fin naturals) (literal : ℕ) (next : Fin labels)
  | copyNat (dst src : Fin naturals) (next : Fin labels)
  | increment (dst : Fin naturals) (next : Fin labels)
  | decrement (dst : Fin naturals) (next : Fin labels)
  | addNat (dst left right : Fin naturals) (next : Fin labels)
  | mulNat (dst left right : Fin naturals) (next : Fin labels)
  | divNat (dst left right : Fin naturals) (next : Fin labels)
  | modNat (dst left right : Fin naturals) (next : Fin labels)
  | lessNat (left right : Fin naturals) (yes no : Fin labels)
  | equalNat (left right : Fin naturals) (yes no : Fin labels)
  | castNat (dst : Fin reals) (src : Fin naturals) (next : Fin labels)
  | setPrecision (src : Fin naturals) (next : Fin labels)
  | input (dst : Fin reals) (address : Fin naturals) (next : Fin labels)
  | read (dst : Fin reals) (address : Fin naturals) (next : Fin labels)
  | write (address : Fin naturals) (src : Fin reals) (next : Fin labels)
  | random (yes no : Fin labels)
  | jump (next : Fin labels)
  | halt (outputBase : Fin naturals)

/-- The first two natural registers hold the dimension and the dyadic
accuracy request exponent. There is always an initial label and at least
two natural registers. -/
structure Program where
  extraLabels : ℕ
  realRegisters : ℕ
  extraNatRegisters : ℕ
  constantCount : ℕ
  constants : Fin constantCount → ℚ
  code : Fin (extraLabels + 1) →
    Instruction (extraLabels + 1) realRegisters
      (extraNatRegisters + 2) constantCount

inductive Status where
  | running
  | halted (outputBase : ℕ)
  | failed
  deriving DecidableEq

structure State (P : Program) where
  label : Fin (P.extraLabels + 1)
  reals : Fin P.realRegisters → Float
  naturals : Fin (P.extraNatRegisters + 2) → ℕ
  memory : ℕ → Float
  precision : Option ℕ
  randomUsed : ℕ
  status : Status

def initial (P : Program) (n requestExponent : ℕ) : State P where
  label := 0
  reals := fun _ => zero
  naturals := fun i => if i = 0 then n else if i = 1 then requestExponent else 0
  memory := fun _ => zero
  precision := none
  randomUsed := 0
  status := .running

/-- Ordinary complex input is read componentwise in row-major order.
Out-of-range addresses return a public zero, never hidden input data. -/
def inputComponent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (address : ℕ) : ℝ :=
  let values := (List.finRange n).flatMap fun i =>
    (List.finRange n).flatMap fun j => [(A i j).re, (A i j).im]
  (values[address]?).getD 0

/-- The only transition that reads the exact mathematical input is
`Instruction.input`, and it returns its rounded component. -/
noncomputable def step {n randomCap : ℕ} (P : Program)
    (A : Matrix (Fin n) (Fin n) ℂ) (bits : Fin randomCap → Bool)
    (s : State P) : State P := by
  classical
  let putReal (dst : Fin P.realRegisters) (x : Float)
      (next : Fin (P.extraLabels + 1)) : State P :=
    {s with label := next, reals := Function.update s.reals dst x}
  let putNat (dst : Fin (P.extraNatRegisters + 2)) (x : ℕ)
      (next : Fin (P.extraLabels + 1)) : State P :=
    {s with label := next, naturals := Function.update s.naturals dst x}
  exact match s.status with
  | .halted _ => s
  | .failed => s
  | .running => match P.code s.label with
    | .constant dst literal next =>
        match s.precision with
        | none => {s with status := .failed}
        | some p => putReal dst (round p (P.constants literal : ℝ)) next
    | .copyReal dst src next => putReal dst (s.reals src) next
    | .addReal dst left right next =>
        match s.precision with
        | none => {s with status := .failed}
        | some p => putReal dst (round p (value (s.reals left) + value (s.reals right))) next
    | .subReal dst left right next =>
        match s.precision with
        | none => {s with status := .failed}
        | some p => putReal dst (round p (value (s.reals left) - value (s.reals right))) next
    | .mulReal dst left right next =>
        match s.precision with
        | none => {s with status := .failed}
        | some p => putReal dst (round p (value (s.reals left) * value (s.reals right))) next
    | .divReal dst left right next =>
        match s.precision with
        | none => {s with status := .failed}
        | some p =>
            if value (s.reals right) = 0 then {s with status := .failed}
            else putReal dst (round p (value (s.reals left) / value (s.reals right))) next
    | .sqrtReal dst src next =>
        match s.precision with
        | none => {s with status := .failed}
        | some p =>
            if value (s.reals src) < 0 then {s with status := .failed}
            else putReal dst (round p (Real.sqrt (value (s.reals src)))) next
    | .lessReal left right yes no =>
        {s with label := if value (s.reals left) < value (s.reals right) then yes else no}
    | .equalReal left right yes no =>
        {s with label := if value (s.reals left) = value (s.reals right) then yes else no}
    | .natural dst literal next => putNat dst literal next
    | .copyNat dst src next => putNat dst (s.naturals src) next
    | .increment dst next => putNat dst (s.naturals dst + 1) next
    | .decrement dst next => putNat dst (s.naturals dst - 1) next
    | .addNat dst left right next => putNat dst (s.naturals left + s.naturals right) next
    | .mulNat dst left right next => putNat dst (s.naturals left * s.naturals right) next
    | .divNat dst left right next =>
        if s.naturals right = 0 then {s with status := .failed}
        else putNat dst (s.naturals left / s.naturals right) next
    | .modNat dst left right next =>
        if s.naturals right = 0 then {s with status := .failed}
        else putNat dst (s.naturals left % s.naturals right) next
    | .lessNat left right yes no =>
        {s with label := if s.naturals left < s.naturals right then yes else no}
    | .equalNat left right yes no =>
        {s with label := if s.naturals left = s.naturals right then yes else no}
    | .castNat dst src next =>
        match s.precision with
        | none => {s with status := .failed}
        | some p => putReal dst (round p (s.naturals src : ℝ)) next
    | .setPrecision src next =>
        if s.precision.isSome ∨ s.naturals src < 2 then {s with status := .failed}
        else {s with label := next, precision := some (s.naturals src)}
    | .input dst address next =>
        match s.precision with
        | none => {s with status := .failed}
        | some p => putReal dst (round p (inputComponent A (s.naturals address))) next
    | .read dst address next => putReal dst (s.memory (s.naturals address)) next
    | .write address src next =>
        {s with label := next, memory := Function.update s.memory (s.naturals address) (s.reals src)}
    | .random yes no =>
        if h : s.randomUsed < randomCap then
          let nextLabel := if bits ⟨s.randomUsed, h⟩ then yes else no
          {s with label := nextLabel, randomUsed := s.randomUsed + 1}
        else {s with status := .failed}
    | .jump next => {s with label := next}
    | .halt outputBase => {s with status := .halted (s.naturals outputBase)}

noncomputable def runSteps {n randomCap : ℕ} (P : Program)
    (A : Matrix (Fin n) (Fin n) ℂ) (requestExponent : ℕ)
    (bits : Fin randomCap → Bool) : ℕ → State P
  | 0 => initial P n requestExponent
  | t + 1 => step P A bits (runSteps P A requestExponent bits t)

/-- A conservative finite charge for each control or scalar operation.
The mantissa width and natural-register/address widths are counted. The
exponent is an unrestricted scale field, as in the specified floating-point
model with sufficient exponent range: charging its binary length would
make the required uniform bound false for arbitrarily tiny legal inputs.
Every operation on an exponent still requires an ordinary instruction;
there is no instruction exposing its bits or using it as a significand. -/
def floatMantissaLength (x : Float) : ℕ :=
  x.mantissa.natAbs.bits.length + 1

def stepCost {P : Program} (s : State P) : ℕ :=
  match s.status with
  | .running =>
      (1 + (s.precision.getD 0) +
        (∑ i : Fin (P.extraNatRegisters + 2),
          ((s.naturals i).bits.length +
            floatMantissaLength (s.memory (s.naturals i)))) +
        (∑ r : Fin P.realRegisters, floatMantissaLength (s.reals r))) ^ 3
  | .halted _ => 0
  | .failed => 0

noncomputable def costThrough {n randomCap : ℕ} (P : Program)
    (A : Matrix (Fin n) (Fin n) ℂ) (requestExponent : ℕ)
    (bits : Fin randomCap → Bool) (steps : ℕ) : ℕ :=
  ∑ t ∈ Finset.range steps,
    stepCost (runSteps P A requestExponent bits t)

/-- A finite dyadic request at exponent `k`; this is the only accuracy
datum visible to the machine. -/
noncomputable def accuracyValue (k : ℕ) : ℝ := (2 : ℝ) ^ (-(k : ℤ))

/-- The output is four stored real components per matrix entry. The
machine must halt with an output base; no arbitrary exact complex output
function is supplied. -/
noncomputable def outputMatrices {n : ℕ} {P : Program} (s : State P) :
    Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ :=
  let base := match s.status with
    | .halted b => b
    | _ => 0
  let Q : Matrix (Fin n) (Fin n) ℂ := fun i j =>
    ⟨value (s.memory (base + 2 * (i.val * n + j.val))),
      value (s.memory (base + 2 * (i.val * n + j.val) + 1))⟩
  let T : Matrix (Fin n) (Fin n) ℂ := fun i j =>
    ⟨value (s.memory (base + 2 * n * n + 2 * (i.val * n + j.val))),
      value (s.memory (base + 2 * n * n + 2 * (i.val * n + j.val) + 1))⟩
  (Q, T)

end NLA.Computation.FiniteFloatMachine
