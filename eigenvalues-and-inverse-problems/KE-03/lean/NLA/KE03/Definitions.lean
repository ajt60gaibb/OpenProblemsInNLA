import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Part

/-!
# KE-03: exact-query algorithm and the original mathematical target

All vector norms are Euclidean. Matrix operator norms are explicitly transported
to Euclidean continuous linear maps. The algorithm receives only an oracle,
`n`, `K`, `ε`, and a finite random seed. Eigenvalues and diagonalizers occur only
in the specification, never in its computational helpers.

`searchNat` is the denotation of testing 0, 1, ... in order. Its domain records
termination; it is not a primitive decision of an existential proposition.
Each predicate supplied by the algorithm is a finite arithmetic comparison.
Real comparison is exact, as allowed by the original query model. No finite
precision, scalar-operation complexity, or bit-complexity claim is made.
-/

noncomputable section

open scoped BigOperators
open Complex

namespace NLA.KE03

abbrev Vec (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def act {n : ℕ} (A : Mat n) : Vec n →L[ℂ] Vec n :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A

def opNorm {n : ℕ} (A : Mat n) : ℝ := ‖act A‖

/-- The supplied conditioning promise; the witnesses are not algorithm inputs. -/
def Conditioned {n : ℕ} (A : Mat n) (K : ℝ) : Prop :=
  ∃ (V W : Mat n) (lam : Fin n → ℂ),
    V * W = 1 ∧ W * V = 1 ∧ A = V * Matrix.diagonal lam * W ∧
      opNorm V * opNorm W ≤ K

/-- An actual eigenvector definition of a complex eigenvalue. -/
def Eigenvalue {n : ℕ} (A : Mat n) (μ : ℂ) : Prop :=
  ∃ v : Vec n, v ≠ 0 ∧ act A v = μ • v

/-- The spectral radius, defined from the actual eigenvalues. -/
def radius {n : ℕ} (A : Mat n) : ℝ :=
  sSup {r : ℝ | ∃ μ : ℂ, Eigenvalue A μ ∧ r = ‖μ‖}

def Successful {n : ℕ} (A : Mat n) (ε : ℝ) (z : ℂ) : Prop :=
  ∃ μ : ℂ, Eigenvalue A μ ∧
    (1 - ε) * radius A ≤ ‖μ‖ ∧ ‖z - μ‖ ≤ ε * radius A

/-- A power-of-two grid admits a fixed finite sequence of fair random bits. -/
def gridSize (n : ℕ) : ℕ := 2 ^ (Nat.log 2 (1024 * n) + 1)

abbrev Seed (n : ℕ) := Fin n → Fin (gridSize n)

def seedVector {n : ℕ} (seed : Seed n) : Vec n :=
  WithLp.toLp 2 fun i => ((seed i).val : ℂ)

/-- Exact uniform probability on a finite seed space. -/
def seedProbability (n : ℕ) (p : Seed n → Prop) : ℝ := by
  classical
  exact (Fintype.card {seed : Seed n // p seed} : ℝ) / Fintype.card (Seed n)

def eta (ε : ℝ) : ℝ := ε ^ 2 / 1024

def distortion (n : ℕ) (K : ℝ) : ℝ := 2 * n * gridSize n * K

/-- Sequential exhaustive search with an explicit termination domain. -/
def searchNat (p : ℕ → Prop) : Part ℕ := by
  classical
  exact ⟨∃ k, p k, fun h => Nat.find h⟩

/-- Positive degree: compute by multiplication and comparison, without logarithms. -/
def degreeSearch (n : ℕ) (K ε : ℝ) : Part ℕ :=
  (searchNat fun k => distortion n K ≤ (1 + eta ε) ^ (k + 1)).map (· + 1)

/-- `history` stores `[A^m b, ..., A b, b]`, using one oracle call per step. -/
def history {n : ℕ} (oracle : Vec n → Vec n) (b : Vec n) : ℕ → List (Vec n)
  | 0 => [b]
  | m + 1 =>
    let h := history oracle b m
    oracle (h.headD 0) :: h

/-- Operational query accounting, with exactly one charged query per transition. -/
inductive QueryTrace {n : ℕ} (oracle : Vec n → Vec n) (b : Vec n) :
    List (Vec n) → ℕ → Prop
  | initial : QueryTrace oracle b [b] 0
  | query {h : List (Vec n)} {q : ℕ} :
      QueryTrace oracle b h q → QueryTrace oracle b (oracle (h.headD 0) :: h) (q + 1)

/-- A finite sum of real squares; no square-root operation is used. -/
def normSq {n : ℕ} (v : Vec n) : ℝ :=
  ∑ i : Fin n, ((v i).re ^ 2 + (v i).im ^ 2)

/-- Evaluate the shifted power from stored responses, without any new query. -/
def shiftedPower {n : ℕ} (h : List (Vec n)) (m : ℕ) (s : ℂ) : Vec n :=
  ∑ j ∈ Finset.range (m + 1),
    ((m.choose j : ℂ) * s ^ (m - j)) • h.getD (m - j) 0

/-- Exhaustive enumeration of positive rational numbers. -/
def positiveRational (k : ℕ) : ℝ :=
  ((Nat.unpair k).1 + 1 : ℝ) / ((Nat.unpair k).2 + 1 : ℝ)

/-- Find a multiplicative approximation by finite exact rational trials. -/
def radiusSearch (m : ℕ) (ε S : ℝ) : Part ℝ :=
  (searchNat fun k =>
    (positiveRational k) ^ (2 * m) ≤ S ∧
      S ≤ ((1 + eta ε) * positiveRational k) ^ (2 * m)).map positiveRational

/-- Search for a sufficiently fine rational stereographic mesh. -/
def meshSearch (ε : ℝ) : Part ℕ :=
  (searchNat fun k => 32 ≤ ε * (k + 1)).map (· + 1)

def circlePoint (t : ℝ) : ℂ :=
  ((1 - t ^ 2 : ℝ) : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ) +
    (((2 * t : ℝ) : ℂ) / ((1 + t ^ 2 : ℝ) : ℂ)) * Complex.I

def circleMesh (q : ℕ) : List ℂ :=
  1 :: (List.range (q + 1)).flatMap (fun j =>
    let u := circlePoint (-1 + 2 * (j : ℝ) / (q : ℝ))
    [u, -u])

/-- Finite comparison, retaining the earlier point in a tie. -/
def selectShift {n : ℕ} (h : List (Vec n)) (m q : ℕ) (r : ℝ) : ℂ := by
  classical
  exact (circleMesh q).foldl (fun best u =>
    if normSq (shiftedPower h m ((r : ℂ) * best)) <
        normSq (shiftedPower h m ((r : ℂ) * u)) then u else best) 1

/-- Every helper after this interface receives only the finite response history. -/
def finish {n : ℕ} (h : List (Vec n)) (m : ℕ) (ε : ℝ) : Part ℂ := by
  classical
  exact if normSq (h.headD 0) = 0 then pure 0 else do
    let r ← radiusSearch m ε (normSq (h.headD 0))
    let q ← meshSearch ε
    pure ((r : ℂ) * selectShift h m q r)

/-- The single uniform randomized exact-query algorithm. The seed is sampled
uniformly, before any oracle responses are observed. -/
def runAlgorithm (n : ℕ) (K ε : ℝ) (oracle : Vec n → Vec n)
    (seed : Seed n) : Part (ℂ × ℕ) := do
  let m ← degreeSearch n K ε
  let h := history oracle (seedVector seed) m
  let z ← finish h m ε
  pure (z, m)

/-- Worst-case query allowance; the logarithm is only in the specification. -/
def queryBound (C : ℝ) (n : ℕ) (K ε : ℝ) : ℝ :=
  C * (1 + Real.log ((n : ℝ) * K)) / ε ^ 2

/-- Full original target, including all-seed termination, actual query traces,
a uniform worst-case query bound, and the required success probability. -/
def SolvesKE03 (C : ℝ) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (K ε : ℝ), 1 ≤ K → 0 < ε → ε < 1 / 2 →
    ∀ (A : Mat n), Conditioned A K → 0 < radius A →
      (∀ seed : Seed n, (runAlgorithm n K ε (act A) seed).Dom) ∧
      (∀ (seed : Seed n) (z : ℂ) (q : ℕ),
        (z, q) ∈ runAlgorithm n K ε (act A) seed →
        QueryTrace (act A) (seedVector seed) (history (act A) (seedVector seed) q) q ∧
          (q : ℝ) ≤ queryBound C n K ε) ∧
      (99 / 100 : ℝ) ≤ seedProbability n (fun seed =>
        ∃ z q, (z, q) ∈ runAlgorithm n K ε (act A) seed ∧ Successful A ε z)

end NLA.KE03
