import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousOn
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! RA-10: the full constant-loss nuclear-error transfer question.
See docs/lean/statements/RA-10/NUMERICAL_TARGETS.md. This defines the original
existential-constant proposition; it does not prove it or claim optimality of
the archived solution's constant 11. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Statements.RA10

/-- The actual nuclear norm: all n singular values of the real matrix acting
between Euclidean spaces. Mathlib's remaining infinitely indexed values are zero. -/
noncomputable def NuclearNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin n, (Matrix.toEuclideanLin M).singularValues i.val

/-- The real PSD order, with symmetry explicit and no entrywise sign restriction. -/
def PositiveSemidefinite {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, M i j = M j i) ∧
    ∀ x : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, x i * M i j * x j

/-- Exact spectral reconstruction from the columns of Q. -/
def SpectralMatrix {n : ℕ} (eigenvalues : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ a, eigenvalues a * Q i a * Q j a

/-- Every allowed ordered orthonormal decomposition is retained, including ties
and zero eigenvalues. The reconstruction equality identifies the given matrix. -/
def OrderedPSDSpectralDecomposition {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (eigenvalues : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ a, 0 ≤ eigenvalues a) ∧ Antitone eigenvalues ∧
    (∀ a b, ∑ i, Q i a * Q i b = if a = b then 1 else 0) ∧
    A = SpectralMatrix eigenvalues Q

/-- Full spectral functional calculus; values of f at negative numbers are unused. -/
def FunctionMatrix {n : ℕ} (f : ℝ → ℝ) (eigenvalues : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  SpectralMatrix (fun a => f (eigenvalues a)) Q

/-- Truncation retains the first k eigenvectors of the explicitly selected basis.
For f 0 > 0, this is not functional calculus on the truncated matrix. -/
def FunctionTruncation {n : ℕ} (k : ℕ) (f : ℝ → ℝ) (eigenvalues : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ a : Fin n,
    if a.val < k then f (eigenvalues a) * Q i a * Q j a else 0

/-- Operator monotonicity on the nonnegative half-line in every real matrix size.
Both PSD arguments and their images are concrete spectral sums, universally
quantified over all their ordered orthonormal decompositions. -/
def OperatorMonotoneOnNonnegative (f : ℝ → ℝ) : Prop :=
  ∀ d : ℕ, 0 < d →
    ∀ H G : Matrix (Fin d) (Fin d) ℝ,
    ∀ eigenvaluesH eigenvaluesG : Fin d → ℝ,
    ∀ QH QG : Matrix (Fin d) (Fin d) ℝ,
      OrderedPSDSpectralDecomposition H eigenvaluesH QH →
      OrderedPSDSpectralDecomposition G eigenvaluesG QG →
      PositiveSemidefinite (H - G) →
      PositiveSemidefinite (FunctionMatrix f eigenvaluesH QH - FunctionMatrix f eigenvaluesG QG)

/-- The original domain: continuity and nonnegativity only on [0,infinity),
together with genuine all-size operator monotonicity. -/
def AdmissibleFunction (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ici 0) ∧
    (∀ x : ℝ, 0 ≤ x → 0 ≤ f x) ∧ OperatorMonotoneOnNonnegative f

/-- The full implication for a fixed universal constant. The same basis is used
in both truncations for each matrix; the two matrices may use independent bases. -/
def TransferBound (C : ℝ) : Prop :=
  ∀ n k : ℕ, 2 ≤ n → 1 ≤ k → k < n →
    ∀ A Ahat : Matrix (Fin n) (Fin n) ℝ,
    ∀ eigenvaluesA eigenvaluesAhat : Fin n → ℝ,
    ∀ QA QAhat : Matrix (Fin n) (Fin n) ℝ,
      OrderedPSDSpectralDecomposition A eigenvaluesA QA →
      OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat →
      ∀ ε : ℝ, 0 ≤ ε → ∀ f : ℝ → ℝ, AdmissibleFunction f →
        NuclearNorm (A - FunctionTruncation k (fun t => t) eigenvaluesAhat QAhat) ≤
            (1 + ε) * NuclearNorm (A - FunctionTruncation k (fun t => t) eigenvaluesA QA) →
        NuclearNorm (FunctionMatrix f eigenvaluesA QA - FunctionTruncation k f eigenvaluesAhat QAhat) ≤
            (1 + C * ε) *
              NuclearNorm (FunctionMatrix f eigenvaluesA QA - FunctionTruncation k f eigenvaluesA QA)

/-- One real constant works for every input, including the function and all
truncation choices. No matrix ordering, gap or positive-tail assumption is added. -/
def Target : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ TransferBound C

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.Statements.RA10
