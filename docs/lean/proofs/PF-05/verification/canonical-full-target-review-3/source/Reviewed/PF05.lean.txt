/- Frozen statement boundary. Changes reopen independent review. -/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! PF-05: equivalence of straight-line infinitesimal rigidity and uniqueness
of real size-two PSD factorizations, including zero entries and singular factors.
See docs/lean/statements/PF-05/NUMERICAL_TARGETS.md.
This defines the complete proposition and does not prove it. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.ReviewedStatements.PF05

def Symmetric {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∀ a b, A a b = A b a

/-- Real symmetry and the ordinary nonnegative quadratic form. -/
def PositiveSemidefinite {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  Symmetric A ∧ ∀ x : Fin k → ℝ, 0 ≤ ∑ a, ∑ b, x a * A a b * x b

/-- A concrete size-k PSD factorization, with ordinary matrix multiplication
and the full diagonal trace. Factors are indexed by the rows and columns of M. -/
def Factorization {p q k : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Matrix (Fin k) (Fin k) ℝ)
    (B : Fin q → Matrix (Fin k) (Fin k) ℝ) : Prop :=
  (∀ i, PositiveSemidefinite (A i)) ∧
  (∀ j, PositiveSemidefinite (B j)) ∧
  ∀ i j, M i j = Matrix.trace (A i * B j)

def HasPSDFactorization {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (k : ℕ) : Prop :=
  ∃ A : Fin p → Matrix (Fin k) (Fin k) ℝ,
    ∃ B : Fin q → Matrix (Fin k) (Fin k) ℝ, Factorization M A B

/-- The source's minimum is over positive factor sizes. Existence at two and
nonexistence at one therefore express PSD rank exactly two. -/
def PSDRankTwo {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) : Prop :=
  HasPSDFactorization M 2 ∧ ¬ HasPSDFactorization M 1

/-- Only the trace derivative vanishes. The actual straight segments remain
PSD for one common interval [0,h); no positive-time exact factorization is required. -/
def FeasibleDirection {p q : ℕ}
    (A E : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B F : Fin q → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (∀ i, Symmetric (E i)) ∧ (∀ j, Symmetric (F j)) ∧
  (∀ i j, Matrix.trace (E i * B j) + Matrix.trace (A i * F j) = 0) ∧
  ∃ h : ℝ, 0 < h ∧ ∀ t : ℝ, 0 ≤ t → t < h →
    (∀ i, PositiveSemidefinite (A i + t • E i)) ∧
    (∀ j, PositiveSemidefinite (B j + t • F j))

/-- A single scalar must generate every row and column direction. -/
def InfinitesimallyRigid {p q : ℕ}
    (A : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B : Fin q → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ E : Fin p → Matrix (Fin 2) (Fin 2) ℝ,
    ∀ F : Fin q → Matrix (Fin 2) (Fin 2) ℝ,
      FeasibleDirection A E B F →
      ∃ d : ℝ, (∀ i, E i = d • A i) ∧ (∀ j, F j = (-d) • B j)

/-- Every alternative factorization is related by one shared real invertible
matrix. The determinant guard makes the matrix inverse the genuine inverse. -/
def UniqueUpToCongruence {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B : Fin q → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ Atilde : Fin p → Matrix (Fin 2) (Fin 2) ℝ,
    ∀ Btilde : Fin q → Matrix (Fin 2) (Fin 2) ℝ,
      Factorization M Atilde Btilde →
      ∃ S : Matrix (Fin 2) (Fin 2) ℝ, S.det ≠ 0 ∧
        (∀ i, Atilde i = S.transpose * A i * S) ∧
        (∀ j, Btilde j = S⁻¹ * B j * (S⁻¹).transpose)

/-- The equivalence for every fixed factorization in the full original domain.
Ordinary rank three excludes empty dimensions without additional restrictions. -/
def Target : Prop :=
  ∀ p q : ℕ, ∀ M : Matrix (Fin p) (Fin q) ℝ,
    (∀ i j, 0 ≤ M i j) → M.rank = 3 → PSDRankTwo M →
    ∀ A : Fin p → Matrix (Fin 2) (Fin 2) ℝ,
      ∀ B : Fin q → Matrix (Fin 2) (Fin 2) ℝ,
        Factorization M A B →
        (InfinitesimallyRigid A B ↔ UniqueUpToCongruence M A B)

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.PF05
