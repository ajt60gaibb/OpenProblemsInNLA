import Mathlib.Data.Nat.Bits
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Matrix.Basic

/-! Fixed prefix-framed binary encodings from the reviewed model specification.
Parsers inspect syntax only. They do not decide regularity, inverse-M promises,
solution cardinality or any other analytic input predicate. No runtime bound
for these Lean functions is asserted: algorithmic costs use FiniteMachine. -/
set_option autoImplicit false

namespace NLA.Computation.BinaryEncoding

abbrev Word := List Bool

/-- MSB first, with exactly one zero bit for zero. -/
def binary (n : ℕ) : Word :=
  if n = 0 then [false] else n.bits.reverse

/-- A unary bit-length prefix, a zero separator, and the binary numeral.
This is not a unary encoding of the value. -/
def encodeNat (n : ℕ) : Word :=
  let bits := binary n
  List.replicate bits.length true ++ [false] ++ bits

def binaryValue (bits : Word) : ℕ :=
  bits.foldl (fun n b => 2 * n + if b then 1 else 0) 0

/-- Count the prefix ones and remove its mandatory separator. -/
def parseLength : Word → Option (ℕ × Word)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (n, tail) ← parseLength rest
      return (n + 1, tail)

/-- Reject truncation, a zero-length numeral, and leading-zero numerals.
The re-encoding equality enforces exactly the chosen canonical convention. -/
def parseNat (w : Word) : Option (ℕ × Word) := do
  let (len, rest) ← parseLength w
  if len = 0 ∨ rest.length < len then none else do
    let bits := rest.take len
    let n := binaryValue bits
    if bits = binary n then some (n, rest.drop len) else none

def encodeInt (z : ℤ) : Word :=
  (decide (z < 0)) :: encodeNat z.natAbs

def parseInt : Word → Option (ℤ × Word)
  | [] => none
  | sign :: rest => do
      let (n, tail) ← parseNat rest
      if sign && n == 0 then none
      else some ((if sign then -(n : ℤ) else (n : ℤ)), tail)

/-- Rational values already carry their normalized coprime numerator and
positive denominator. Zero is necessarily encoded as 0/1. -/
def encodeRat (q : ℚ) : Word :=
  encodeInt q.num ++ encodeNat q.den

def parseRat (w : Word) : Option (ℚ × Word) := do
  let (num, rest) ← parseInt w
  let (den, tail) ← parseNat rest
  if den = 0 ∨ num.natAbs.gcd den ≠ 1 then none
  else some (mkRat num den, tail)

def encodeRats (values : List ℚ) : Word :=
  values.flatMap encodeRat

private def parseRatsAux : ℕ → Word → Option (List ℚ × Word)
  | 0, w => some ([], w)
  | k + 1, w => do
      let (q, rest) ← parseRat w
      let (qs, tail) ← parseRatsAux k rest
      return (q :: qs, tail)

/-- Reject impossible field counts before recursion or dimension-based
allocation. Every rational consumes at least one bit (in fact at least seven). -/
def parseRats (count : ℕ) (w : Word) : Option (List ℚ × Word) :=
  if count ≤ w.length then parseRatsAux count w else none

private theorem parseRatsAux_length (count : ℕ) (w : Word) (values : List ℚ)
    (tail : Word) (h : parseRatsAux count w = some (values, tail)) :
    values.length = count := by
  induction count generalizing w values tail with
  | zero =>
      simp only [parseRatsAux, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      rfl
  | succ count ih =>
      cases first : parseRat w with
      | none => simp [parseRatsAux, first] at h
      | some entry =>
          rcases entry with ⟨q, rest⟩
          cases remaining : parseRatsAux count rest with
          | none => simp [parseRatsAux, first, remaining] at h
          | some result =>
              rcases result with ⟨qs, suffix⟩
              have len := ih rest qs suffix remaining
              simp [parseRatsAux, first, remaining] at h
              rw [← h.1]
              simpa using congrArg Nat.succ len

/-- A successful fixed-count parse has exactly that many fields. Thus the
matrix/vector constructors never obtain missing coefficients from `getD`. -/
theorem parseRats_length (count : ℕ) (w : Word) (values : List ℚ) (tail : Word)
    (h : parseRats count w = some (values, tail)) : values.length = count := by
  unfold parseRats at h
  split at h
  · exact parseRatsAux_length count w values tail h
  · contradiction

def matrixEntries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : List ℚ :=
  (List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin n => A i j))).flatten

def vectorEntries {n : ℕ} (b : Fin n → ℚ) : List ℚ := List.ofFn b

private def matrixFromEntries (n : ℕ) (xs : List ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => xs.getD (i.val * n + j.val) 0

private def vectorFromEntries (n : ℕ) (xs : List ℚ) : Fin n → ℚ :=
  fun i => xs.getD i.val 0

/-- This is syntax, not the n>=1 mathematical promise. -/
structure AVInput where
  n : ℕ
  matrix : Matrix (Fin n) (Fin n) ℚ
  rhs : Fin n → ℚ

def encodeAV (a : AVInput) : Word :=
  encodeNat a.n ++ encodeRats (matrixEntries a.matrix) ++ encodeRats (vectorEntries a.rhs)

def decodeAV (w : Word) : Option AVInput := do
  let (n, rest) ← parseNat w
  let (entries, rest) ← parseRats (n * n) rest
  let (rhs, tail) ← parseRats n rest
  if tail = [] then some ⟨n, matrixFromEntries n entries, vectorFromEntries n rhs⟩ else none

structure ThresholdInput where
  n : ℕ
  matrix : Matrix (Fin n) (Fin n) ℚ
  threshold : ℚ

def encodeThreshold (a : ThresholdInput) : Word :=
  encodeNat a.n ++ encodeRats (matrixEntries a.matrix) ++ encodeRat a.threshold

def decodeThreshold (w : Word) : Option ThresholdInput := do
  let (n, rest) ← parseNat w
  let (entries, rest) ← parseRats (n * n) rest
  let (threshold, tail) ← parseRat rest
  if tail = [] then some ⟨n, matrixFromEntries n entries, threshold⟩ else none

structure IntervalInput where
  n : ℕ
  lowerMatrix : Matrix (Fin n) (Fin n) ℚ
  upperMatrix : Matrix (Fin n) (Fin n) ℚ
  lowerRhs : Fin n → ℚ
  upperRhs : Fin n → ℚ

def encodeInterval (a : IntervalInput) : Word :=
  encodeNat a.n ++ encodeRats (matrixEntries a.lowerMatrix) ++
    encodeRats (matrixEntries a.upperMatrix) ++
    encodeRats (vectorEntries a.lowerRhs) ++ encodeRats (vectorEntries a.upperRhs)

def decodeInterval (w : Word) : Option IntervalInput := do
  let (n, rest) ← parseNat w
  let (lo, rest) ← parseRats (n * n) rest
  let (hi, rest) ← parseRats (n * n) rest
  let (l, rest) ← parseRats n rest
  let (u, tail) ← parseRats n rest
  if tail = [] then
    some ⟨n, matrixFromEntries n lo, matrixFromEntries n hi,
      vectorFromEntries n l, vectorFromEntries n u⟩
  else none

structure IntervalOutput where
  n : ℕ
  lower : Fin n → ℚ
  upper : Fin n → ℚ

/-- Output dimension is explicit and must equal the input dimension when
the problem's semantic output relation is imposed. All endpoint bits count. -/
def encodeIntervalOutput (a : IntervalOutput) : Word :=
  encodeNat a.n ++ encodeRats (vectorEntries a.lower) ++ encodeRats (vectorEntries a.upper)

def decodeIntervalOutput (w : Word) : Option IntervalOutput := do
  let (n, rest) ← parseNat w
  let (lo, rest) ← parseRats n rest
  let (hi, tail) ← parseRats n rest
  if tail = [] then some ⟨n, vectorFromEntries n lo, vectorFromEntries n hi⟩ else none

/-- The fixed NP witness-pair syntax; no ignored suffix or implicit delimiter. -/
def encodePair (w certificate : Word) : Word :=
  encodeNat w.length ++ w ++ encodeNat certificate.length ++ certificate

end NLA.Computation.BinaryEncoding
