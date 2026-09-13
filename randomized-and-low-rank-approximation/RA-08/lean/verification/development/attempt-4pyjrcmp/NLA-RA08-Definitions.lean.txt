/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Proof-independent statement boundary for Matthew J. Colbrook's RA-08
counterexample. Formalization affiliation: Department of Computing and
Mathematical Sciences, California Institute of Technology, Pasadena,
California, USA. No theorem implementation is imported here.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false
open scoped BigOperators Classical MatrixOrder
noncomputable section

namespace NLA.RA08

abbrev RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The actual operator norm for the matrix acting on real Euclidean space.
This is not the default norm on a matrix or on a function space. -/
def spectralNorm {n : ℕ} (A : RealMatrix n) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖

/-- Exactly the function class in the canonical problem. A function on the
nonnegative half-line is represented by an arbitrary real extension. Values
at negative arguments are unconstrained; no `f 0 = 0` premise is imposed. -/
def AdmissibleFunction (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) f ∧
    MonotoneOn f (Set.Ici 0) ∧ ∀ x : ℝ, 0 ≤ x → 0 ≤ f x

/-- An arbitrary complete ordered orthonormal eigendecomposition of the
actual matrix. Over the reals a unitary matrix is an orthogonal matrix.
Both the nonnegative eigenvalues and every permitted choice of eigenvectors
are quantified in the conjecture; no preferred choice is built in.
Reconstruction, not a claimed numerical spectrum, is part of the data. -/
structure OrderedSpectralData {n : ℕ} (A : RealMatrix n) where
  eigenvalues : Fin n → ℝ
  orthogonal : Matrix.unitaryGroup (Fin n) ℝ
  decreasing : Antitone eigenvalues
  nonnegative : ∀ i, 0 ≤ eigenvalues i
  reconstruct : A =
    (orthogonal : RealMatrix n) * Matrix.diagonal eigenvalues *
      (orthogonal : RealMatrix n).transpose

/-- Apply arbitrary scalar values in the selected eigenbasis. -/
def spectralCombination {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (values : Fin n → ℝ) : RealMatrix n :=
  (d.orthogonal : RealMatrix n) * Matrix.diagonal values *
    (d.orthogonal : RealMatrix n).transpose

/-- Canonical rank-`k` eigenvalue truncation, zero-based indices `i < k`. -/
def truncation {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (k : ℕ) : RealMatrix n :=
  spectralCombination d (fun i => if i.val < k then d.eigenvalues i else 0)

/-- Genuine real continuous functional calculus in the real matrix algebra. -/
def functionalCalculus {n : ℕ} (f : ℝ → ℝ) (A : RealMatrix n) : RealMatrix n :=
  cfc (R := ℝ) f A

/-- The function truncation uses the SAME selected eigenvectors as `truncation`.
It is neither `f (X_k)` nor an independently rotated spectral truncation of `f X`.
In particular the discarded entries are zero even when `f 0` is positive. -/
def functionTruncation {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) (k : ℕ) : RealMatrix n :=
  spectralCombination d (fun i => if i.val < k then f (d.eigenvalues i) else 0)

/-- Complete original RA-08 assertion, including every real symmetric PSD pair,
every original dimension/rank/error parameter, every admissible scalar function,
and every allowed ordered eigendecomposition. The matrix order is PSD order. -/
def ConcaveSpectralTransferConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n →
    ∀ A Ahat : RealMatrix n, A.PosSemidef → Ahat.PosSemidef → Ahat ≤ A →
      ∀ f : ℝ → ℝ, AdmissibleFunction f →
        ∀ dA : OrderedSpectralData A, ∀ dAhat : OrderedSpectralData Ahat,
          ∀ ε : ℝ, 0 ≤ ε →
            spectralNorm (A - truncation dAhat k) ≤
                (1 + ε) * spectralNorm (A - truncation dA k) →
            spectralNorm (functionalCalculus f A - functionTruncation dAhat f k) ≤
                (1 + ε) *
                  spectralNorm (functionalCalculus f A - functionTruncation dA f k)

/-- Colbrook's unchanged kink function, restricted to the half-line in the problem. -/
def witnessFunction (x : ℝ) : ℝ := min x 1

def witnessT : ℝ := 1 / 65536

def witnessA : ℝ := 17 / 16

def witnessB : ℝ := 127 / 128

/-- The source's exact two orthonormal columns. -/
def witnessU : Matrix (Fin 3) (Fin 2) ℝ :=
  (1 / 9 : ℝ) • !![1, 8; 8, 1; -4, 4]

/-- The unchanged rank-three orthogonal projection, written with the single
common denominator `65 * 81`. The source gives the equivalent `U Uᵀ` block form. -/
def witnessF : RealMatrix 6 :=
  (1 / 5265 : ℝ) •
    !![4160, 1024, 1792, 72, 576, 0;
       1024, 4160, -1792, 576, 72, 0;
       1792, -1792, 2048, -288, 288, 0;
       72, 576, -288, 81, 0, 0;
       576, 72, 288, 0, 81, 0;
       0, 0, 0, 0, 0, 5265]

def witnessApproximation : RealMatrix 6 :=
  Matrix.diagonal ![1 / 2, witnessB, witnessA, 0, 0, 0]

def witnessMatrix : RealMatrix 6 :=
  witnessApproximation + witnessT • witnessF

/-- The exact CFC image of the approximation is a conclusion to be proved. -/
def witnessApproximationImage : RealMatrix 6 :=
  Matrix.diagonal ![1 / 2, witnessB, 1, 0, 0, 0]

/-- An unnormalized vector avoids every numerical square-root computation. -/
def witnessVector : Fin 6 → ℝ := ![4, 3, 1, 0, 0, 0]

def minorantCoefficient : ℝ := 67108864 / 1896129

/-- A new exact proof route for the unchanged source witness. This polynomial
is a scalar minorant only on the spectral set that must actually be proved. -/
def minorantFunction (x : ℝ) : ℝ :=
  x - minorantCoefficient * x ^ 2 * (x - 1 / 2) ^ 2 * (x - witnessB) ^ 2

/-- Three commuting matrix factors. Its application to one vector is the
only degree-three matrix-vector computation required by the rational certificate. -/
def matrixK {n : ℕ} (A : RealMatrix n) : RealMatrix n :=
  A * (A - (1 / 2 : ℝ) • (1 : RealMatrix n)) *
    (A - witnessB • (1 : RealMatrix n))

/-- Named polynomial matrix expression; its equality with genuine CFC is a
proof obligation, not a definition of the continuous functional calculus. -/
def minorantMatrix {n : ℕ} (A : RealMatrix n) : RealMatrix n :=
  A - minorantCoefficient • (matrixK A) ^ 2

/-- Exact expected result of the three matrix-vector products. -/
def witnessKVector : Fin 6 → ℝ :=
  ![-119989013011 / 10452232411545600,
    2434900073263 / 167235718584729600,
    1756776553030423 / 41808929646182400,
    -24520157 / 743269860376576,
    14703909709 / 445961916225945600,
    0]

/-- A weaker strict gap than the manuscript's contour estimate, sufficient
for the complete original negative answer. It will use a material, explicit
kernel-only LeanCert point certificate, not an eigenvalue interval computation. -/
def witnessGap : ℝ :=
  78605142319958855341529309 / 11432529876841442781954048000

end NLA.RA08
