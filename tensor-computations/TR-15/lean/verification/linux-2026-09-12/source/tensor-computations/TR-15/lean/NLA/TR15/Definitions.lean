import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Lean.Elab.Tactic.Omega

/-!
# TR-15: the complete Hankel H-eigenvalue inheritance statement

Mathematical counterexample: Matthew J. Colbrook, 11 September 2026.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.
AI-assisted formalization; independent review is recorded separately.

All tensor indices are zero-based. An order `s`, dimension `N` tensor is the
full finite array on `Fin s → Fin N`. Its Hankel entry is the generating vector
at the sum of the indices. This is exactly the canonical one-based index sum
minus `s`; no spectral or contraction equations are built into the definitions.
-/

set_option autoImplicit false

open scoped BigOperators

namespace NLA.TR15

noncomputable section

/-- A real tensor with `s` slots, each of dimension `N`. -/
abbrev Tensor (s N : ℕ) := (Fin s → Fin N) → ℝ

/-- Sum of zero-based tensor indices as an actual index into the finite
generating vector. The proof establishes the bound, without a default value. -/
def generatorIndex {s N : ℕ} (indices : Fin s → Fin N) :
    Fin (s * (N - 1) + 1) :=
  ⟨∑ j, (indices j).val, by
    have hle : (∑ j : Fin s, (indices j).val) ≤ s * (N - 1) := by
      calc
        (∑ j : Fin s, (indices j).val) ≤ ∑ _j : Fin s, (N - 1) :=
          Finset.sum_le_sum (fun j _ => Nat.le_sub_one_of_lt (indices j).isLt)
        _ = s * (N - 1) := by simp
    omega⟩

/-- Every entry is taken from the same finite generating vector. -/
def hankelTensor (s N : ℕ) (h : Fin (s * (N - 1) + 1) → ℝ) : Tensor s N :=
  fun indices => h (generatorIndex indices)

/-- Prepend the uncontracted coordinate to the `s-1` contracted indices.
For positive order this is the usual tuple `(i, indices 0, …)`.
The total definition at order zero is never used by the conjecture. -/
def prependIndex {s N : ℕ} (i : Fin N) (indices : Fin (s - 1) → Fin N) :
    Fin s → Fin N :=
  fun j => if hj : j.val = 0 then i else
    indices ⟨j.val - 1, by have := j.isLt; omega⟩

/-- The full H-eigenvalue contraction: sum over all ordered `(s-1)`-tuples,
with one factor of `x` for each contracted slot. There are no multinomial
weights because every ordered tuple appears separately. -/
def contraction {s N : ℕ} (T : Tensor s N) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => ∑ indices : Fin (s - 1) → Fin N,
    T (prependIndex i indices) * ∏ j : Fin (s - 1), x (indices j)

/-- A genuine real H-eigenpair, including the nonzero-vector requirement. -/
def IsHEigenpair {s N : ℕ} (T : Tensor s N) (eigenvalue : ℝ)
    (x : Fin N → ℝ) : Prop :=
  x ≠ 0 ∧ ∀ i, contraction T x i = eigenvalue * x i ^ (s - 1)

/-- Every real H-eigenpair has a nonnegative real eigenvalue. This is exactly
the canonical absence of a negative real H-eigenvalue; existence is not assumed. -/
def HasNoNegativeHEigenvalues {s N : ℕ} (T : Tensor s N) : Prop :=
  ∀ (eigenvalue : ℝ) (x : Fin N → ℝ), IsHEigenpair T eigenvalue x →
    0 ≤ eigenvalue

/-- The original lower tensor: order `m`, dimension `q*(n-1)+1`.
The finite cast only identifies the equal generating-vector lengths. -/
def lowerTensor (m q n : ℕ) (h : Fin (q * m * (n - 1) + 1) → ℝ) :
    Tensor m (q * (n - 1) + 1) :=
  hankelTensor m (q * (n - 1) + 1)
    (fun i => h (Fin.cast (by simp [Nat.mul_comm, Nat.mul_assoc]) i))

/-- The original higher tensor: order `q*m`, dimension `n`, using exactly `h`. -/
def upperTensor (m q n : ℕ) (h : Fin (q * m * (n - 1) + 1) → ℝ) :
    Tensor (q * m) n :=
  hankelTensor (q * m) n h

/-- Every parameter restriction from the original conjecture. -/
def Admissible (m q n : ℕ) : Prop :=
  Odd m ∧ 3 ≤ m ∧ 2 ≤ q ∧ 2 ≤ n

/-- The full original universal inheritance conjecture over real data.
It contains no positivity, strong-Hankel, or eigenpair-existence assumption. -/
def InheritanceConjecture : Prop :=
  ∀ (m q n : ℕ), Admissible m q n →
    ∀ h : Fin (q * m * (n - 1) + 1) → ℝ,
      HasNoNegativeHEigenvalues (lowerTensor m q n h) →
        HasNoNegativeHEigenvalues (upperTensor m q n h)

/-- Colbrook's seven exact common generators, in zero-based order. -/
def witnessGenerator : Fin 7 → ℝ := ![2, 0, 1, 0, 2, 0, -1]

def witnessLower : Tensor 3 3 := lowerTensor 3 2 2 witnessGenerator

def witnessUpper : Tensor 6 2 := upperTensor 3 2 2 witnessGenerator

def witnessUpperVector : Fin 2 → ℝ := ![0, 1]

/-- Polynomial used only to establish a real lower-order eigenpair by IVT. -/
def rootPolynomial (t : ℝ) : ℝ := 2 * t ^ 4 + 2 * t ^ 3 + 3 * t ^ 2 - 4 * t - 1

def lowerEigenvalue (t : ℝ) : ℝ := 2 + 2 * t + 2 * t ^ 2

def lowerEigenvector (t : ℝ) : Fin 3 → ℝ := ![1, 0, t]

end

end NLA.TR15
