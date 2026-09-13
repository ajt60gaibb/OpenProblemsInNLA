/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Mathematical theorem: Matthew J. Colbrook. Original question: Persson–Meyer–Musco.
Spectral-data/CFC design adapted from the campaign's proof-independent RA08
statement definitions; no RA08 implementation or admitted theorem is imported.
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
namespace NLA.RA09

abbrev RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Finite real entry squares; equality with actual Frobenius norm squared is an obligation. -/
def frobeniusSquared {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

section FrobeniusInstance
open scoped Matrix.Norms.Frobenius
/-- The actual Mathlib Frobenius norm, with its instance isolated from CFC. -/
def frobeniusNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ‖A‖
end FrobeniusInstance

/-- Exactly the canonical half-line function class, with arbitrary extension below zero. -/
def AdmissibleFunction (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) f ∧
    MonotoneOn f (Set.Ici 0) ∧ ∀ x : ℝ, 0 ≤ x → 0 ≤ f x

/-- Every allowed ordered orthonormal decomposition of the actual matrix. -/
structure OrderedSpectralData {n : ℕ} (A : RealMatrix n) where
  eigenvalues : Fin n → ℝ
  orthogonal : Matrix.unitaryGroup (Fin n) ℝ
  decreasing : Antitone eigenvalues
  nonnegative : ∀ i, 0 ≤ eigenvalues i
  reconstruct : A =
    (orthogonal : RealMatrix n) * Matrix.diagonal eigenvalues *
      (orthogonal : RealMatrix n).transpose

def spectralCombination {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (values : Fin n → ℝ) : RealMatrix n :=
  (d.orthogonal : RealMatrix n) * Matrix.diagonal values *
    (d.orthogonal : RealMatrix n).transpose

def truncation {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (k : ℕ) : RealMatrix n :=
  spectralCombination d (fun i => if i.val < k then d.eigenvalues i else 0)

/-- Genuine Mathlib real functional calculus, not a stipulated spectral formula. -/
def functionalCalculus {n : ℕ} (f : ℝ → ℝ) (A : RealMatrix n) : RealMatrix n :=
  cfc (R := ℝ) f A

/-- SAME basis as the original truncation; discarded entries stay zero even when f(0)>0. -/
def functionTruncation {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) (k : ℕ) : RealMatrix n :=
  spectralCombination d (fun i => if i.val < k then f (d.eigenvalues i) else 0)

def spectralTail {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), d.eigenvalues i ^ 2

def functionTail {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), f (d.eigenvalues i) ^ 2

def overlapMatrix {n : ℕ} {A Ahat : RealMatrix n}
    (dA : OrderedSpectralData A) (dHat : OrderedSpectralData Ahat) : RealMatrix n :=
  (dA.orthogonal : RealMatrix n).transpose * (dHat.orthogonal : RealMatrix n)

def overlapWeights {n : ℕ} {A Ahat : RealMatrix n}
    (dA : OrderedSpectralData A) (dHat : OrderedSpectralData Ahat) : RealMatrix n :=
  fun i j => overlapMatrix dA dHat i j ^ 2

/-- The actual rank-one real outer product. -/
def outerSquare {n : ℕ} (v : Fin n → ℝ) : RealMatrix n := fun i j => v i * v j

def transferScale (f : ℝ → ℝ) (τ : ℝ) : ℝ := f τ / τ
def scalarAuxiliary (f : ℝ → ℝ) (τ a : ℝ) : ℝ :=
  max ((transferScale f τ)^2 * a^2 - (f a)^2) 0
def branchQuadratic (d z : ℝ) : ℝ := 2*(d+1)*z^2 - (2*d+1)*z + d

/-- Complete original assertion: the premise is the difference of squared norms,
not a substituted residual premise. Every permitted eigenbasis is quantified. -/
def ConcaveFrobeniusTransferConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n →
    ∀ A Ahat : RealMatrix n, A.PosSemidef → Ahat.PosSemidef → Ahat ≤ A →
      ∀ f : ℝ → ℝ, AdmissibleFunction f →
        ∀ dA : OrderedSpectralData A, ∀ dHat : OrderedSpectralData Ahat,
          ∀ ε : ℝ, 0 ≤ ε →
            frobeniusSquared A - frobeniusSquared (truncation dHat k) ≤
                (1+ε) * frobeniusSquared (A - truncation dA k) →
            frobeniusSquared (functionalCalculus f A - functionTruncation dHat f k) ≤
                (1+ε) * frobeniusSquared (functionalCalculus f A - functionTruncation dA f k)

end NLA.RA09
