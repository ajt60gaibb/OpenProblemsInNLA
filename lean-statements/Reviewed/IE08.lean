/- Frozen statement boundary. Changes reopen independent review. -/
import Mathlib
import NLA.Computation.FiniteFloatMachine
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! IE-08: a uniform randomized finite-code rounded floating-point Schur
algorithm with worst-case work and precision caps. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Classical
open scoped BigOperators
open NLA.Computation.FiniteFloatMachine

namespace NLA.ReviewedStatements.IE08

/-- The Euclidean norm on a complex coordinate vector. -/
noncomputable def vectorNorm {n : ℕ} (x : Fin n → ℂ) : ℝ :=
  Real.sqrt (∑ i : Fin n, Complex.normSq (x i))

def action {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (x : Fin n → ℂ) : Fin n → ℂ :=
  fun i => ∑ j : Fin n, A i j * x j

/-- The true induced complex Euclidean operator norm, including n = 1. -/
noncomputable def spectralNorm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ x : Fin n → ℂ,
    vectorNorm x ≤ 1 ∧ r = vectorNorm (action A x)}

/-- A finite dyadic request supplied externally to the machine. It
undershoots the requested real accuracy by at most a factor of two. -/
noncomputable def AccuracyEncoding (δ : ℝ) (k : ℕ) : Prop :=
  δ / 2 ≤ accuracyValue k ∧ accuracyValue k ≤ δ

/-- The dyadic input interface covers every real requested accuracy. -/
def AccuracyBridge : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
    ∃ k : ℕ, AccuracyEncoding δ k

/-- The exact semantic rule of the scalar floating-point primitive must
produce p-bit significands and the usual relative-error estimate. -/
noncomputable def RoundedPrimitiveCorrect : Prop :=
  ∀ (p : ℕ), 2 ≤ p → ∀ (x : ℝ),
    MantissaFits p (round p x) ∧
    |value (round p x) - x| ≤ (2 : ℝ) ^ (-(p : ℤ)) * |x|

/-- A floor of the real asymptotic work cap makes the finite-bit bound no
larger than the stated real-valued bound. -/
noncomputable def workBudget (C : ℝ) (c n : ℕ) (δ : ℝ) : ℕ :=
  Nat.floor (C * (n : ℝ) ^ 3 * (Real.log ((n : ℝ) / δ)) ^ c)

def UpperTriangular {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i j : Fin n, j < i → T i j = 0

/-- A valid execution halts on every bit tape, stays within the charged
worst-case work and mantissa bounds, and returns structurally exact
zeros below the diagonal. The selected precision is fixed for the run. -/
noncomputable def RunOK {n : ℕ} (P : Program)
    (A : Matrix (Fin n) (Fin n) ℂ) (k budget : ℕ)
    (precisionCap : ℝ) (bits : Fin budget → Bool) : Prop :=
  let final := runSteps P A k bits budget
  (∃ base : ℕ, final.status = .halted base) ∧
  (∃ p : ℕ, 2 ≤ p ∧ final.precision = some p ∧
    (p : ℝ) ≤ precisionCap) ∧
  costThrough P A k bits budget ≤ budget ∧
  (∀ t : ℕ, t ≤ budget →
    ∀ p : ℕ, (runSteps P A k bits t).precision = some p →
      (∀ r : Fin P.realRegisters,
        MantissaFits p ((runSteps P A k bits t).reals r)) ∧
      (∀ address : ℕ,
        MantissaFits p ((runSteps P A k bits t).memory address))) ∧
  UpperTriangular (outputMatrices (n := n) final).2

/-- Both original spectral-norm residuals must hold in the same run,
against the exact original input matrix rather than its rounded copy. -/
noncomputable def Successful {n : ℕ} (P : Program)
    (A : Matrix (Fin n) (Fin n) ℂ) (k budget : ℕ)
    (δ : ℝ) (bits : Fin budget → Bool) : Prop :=
  let final := runSteps P A k bits budget
  let Q := (outputMatrices (n := n) final).1
  let T := (outputMatrices (n := n) final).2
  spectralNorm (A - Q * T * Q.conjTranspose) ≤ δ ∧
    spectralNorm (Q.conjTranspose * Q - 1) ≤ δ

/-- Uniform probability over the complete finite bit tape, including
every failed, capped, or otherwise unsuccessful execution. -/
noncomputable def successProbability {n : ℕ} (P : Program)
    (A : Matrix (Fin n) (Fin n) ℂ) (k budget : ℕ) (δ : ℝ) : ℝ :=
  ((Finset.univ.filter (fun bits : Fin budget → Bool =>
      Successful P A k budget δ bits)).card : ℝ) /
    (Fintype.card (Fin budget → Bool) : ℝ)

/-- One finite program and universal constants work for every dimension,
real tolerance, valid finite dyadic request, and complex matrix of norm at
most one. Its random source is a finite tape with a deterministic cap. -/
noncomputable def Target : Prop :=
  RoundedPrimitiveCorrect ∧ AccuracyBridge ∧
  ∃ P : Program, ∃ Cwork Cprecision : ℝ,
    0 < Cwork ∧ 0 < Cprecision ∧
    ∃ c : ℕ, 1 ≤ c ∧ ∀ n : ℕ, 0 < n →
      ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        ∀ k : ℕ, AccuracyEncoding δ k →
          ∀ A : Matrix (Fin n) (Fin n) ℂ,
            spectralNorm A ≤ 1 →
              let budget := workBudget Cwork c n δ
              (∀ bits : Fin budget → Bool,
                RunOK P A k budget
                  (Cprecision * Real.log ((n : ℝ) / δ)) bits) ∧
              successProbability P A k budget δ ≥ 99 / 100

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.IE08
