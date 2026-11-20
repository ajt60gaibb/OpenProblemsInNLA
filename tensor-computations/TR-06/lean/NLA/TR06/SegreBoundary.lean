/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original TR-06 mathematical proof: Matthew J. Colbrook.
Proposed auxiliary statement boundary only: no theorem proofs are implemented.
-/
import NLA.TR06.Complexification
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Option

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.TR06.Segre

/-- One amplitude and all non-anchor factor entries for each summand. -/
abbrev Coordinate {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (q₀ : Fin r → TensorIndex d n) :=
  (i : Fin r) × Option ((j : Fin d) × {u : Fin (n j) // u ≠ q₀ i j})

/-- Actual Euclidean coordinate space, not the redundant factor-vector space. -/
abbrev Parameter (𝕜 : Type*) [RCLike 𝕜] {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (q₀ : Fin r → TensorIndex d n) := EuclideanSpace 𝕜 (Coordinate q₀)

variable {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

def factor (q₀ : Fin r → TensorIndex d n) (z : Parameter 𝕜 q₀)
    (i : Fin r) (j : Fin d) (u : Fin (n j)) : 𝕜 :=
  if h : u = q₀ i j then 1 else z ⟨i, some ⟨j, ⟨u, h⟩⟩⟩

def summands (q₀ : Fin r → TensorIndex d n) (z : Parameter 𝕜 q₀) :
    Fin r → Tensor 𝕜 d n :=
  fun i => z ⟨i, none⟩ • pureTensor (factor q₀ z i)

def sum (q₀ : Fin r → TensorIndex d n) (z : Parameter 𝕜 q₀) : Tensor 𝕜 d n :=
  ∑ i, summands q₀ z i

def factorPolynomial (𝕜 : Type*) [RCLike 𝕜]
    (q₀ : Fin r → TensorIndex d n) (i : Fin r) (j : Fin d) (u : Fin (n j)) :
    MvPolynomial (Coordinate q₀) 𝕜 :=
  if h : u = q₀ i j then 1 else MvPolynomial.X ⟨i, some ⟨j, ⟨u, h⟩⟩⟩

def summandPolynomial (𝕜 : Type*) [RCLike 𝕜]
    (q₀ : Fin r → TensorIndex d n) (i : Fin r) (q : TensorIndex d n) :
    MvPolynomial (Coordinate q₀) 𝕜 :=
  MvPolynomial.X ⟨i, none⟩ * ∏ j, factorPolynomial 𝕜 q₀ i j (q j)

def sumPolynomial (𝕜 : Type*) [RCLike 𝕜]
    (q₀ : Fin r → TensorIndex d n) (q : TensorIndex d n) :
    MvPolynomial (Coordinate q₀) 𝕜 := ∑ i, summandPolynomial 𝕜 q₀ i q

def pullback (q₀ : Fin r → TensorIndex d n) (p : MvPolynomial (TensorIndex d n) 𝕜) :
    MvPolynomial (Coordinate q₀) 𝕜 :=
  MvPolynomial.bind₁ (sumPolynomial 𝕜 q₀) p

def amplitudesPolynomial (𝕜 : Type*) [RCLike 𝕜]
    (q₀ : Fin r → TensorIndex d n) : MvPolynomial (Coordinate q₀) 𝕜 :=
  ∏ i : Fin r, MvPolynomial.X ⟨i, none⟩

/-- Required exact coordinate count and dimension, for every prescribed pattern. -/
def DimensionStatement : Prop :=
  ∀ (d : ℕ) (n : Fin d → ℕ) (r : ℕ) (q₀ : Fin r → TensorIndex d n),
    Fintype.card (Coordinate q₀) = expectedDimension d n r ∧
    Module.finrank ℝ (Parameter ℝ q₀) = expectedDimension d n r ∧
    Module.finrank ℂ (Parameter ℂ q₀) = expectedDimension d n r

/-- Polynomial formulas must evaluate to the actual tensor maps. -/
def EvaluationStatement : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (d : ℕ) (n : Fin d → ℕ) (r : ℕ)
    (q₀ : Fin r → TensorIndex d n) (z : Parameter 𝕜 q₀),
    (∀ i q, MvPolynomial.eval (fun c => z c) (summandPolynomial 𝕜 q₀ i q) =
      summands q₀ z i q) ∧
    (∀ q, MvPolynomial.eval (fun c => z c) (sumPolynomial 𝕜 q₀ q) = sum q₀ z q) ∧
    (∀ p : MvPolynomial (TensorIndex d n) 𝕜,
      MvPolynomial.eval (fun c => z c) (pullback q₀ p) =
        MvPolynomial.eval (fun q => sum q₀ z q) p)

/-- Positive mode count lets one absorb amplitude into one factor. -/
def DecompositionStatement : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (d : ℕ) (n : Fin d → ℕ) (r : ℕ)
    (_hd : 0 < d) (q₀ : Fin r → TensorIndex d n) (z : Parameter 𝕜 q₀),
    (∀ i, z ⟨i, none⟩ ≠ 0) →
      Decomposes (summands q₀ z) (sum q₀ z) ∧
      (∀ i, summands q₀ z i (q₀ i) = z ⟨i, none⟩)

/-- Every actual decomposition with these nonzero pivots is represented. -/
def RepresentationStatement : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (d : ℕ) (n : Fin d → ℕ) (r : ℕ)
    (q₀ : Fin r → TensorIndex d n) (a : Fin r → Tensor 𝕜 d n),
    (∀ i, RankOne (a i)) → (∀ i, a i (q₀ i) ≠ 0) →
      ∃ z : Parameter 𝕜 q₀, (∀ i, z ⟨i, none⟩ ≠ 0) ∧ summands q₀ z = a

/-- The witness need not use the prescribed pivots; the conclusion is required
for EVERY prescribed pivot pattern. No genericity/exact-rank hypothesis is added. -/
def NonzeroPullbackStatement : Prop :=
  ∀ (d : ℕ) (n : Fin d → ℕ) (r : ℕ)
    (q₀ : Fin r → TensorIndex d n) (p : MvPolynomial (TensorIndex d n) ℂ)
    (A : Tensor ℂ d n) (a : Fin r → Tensor ℂ d n),
    Decomposes a A → MvPolynomial.eval (fun q => A q) p ≠ 0 →
      pullback q₀ p ≠ 0 ∧ amplitudesPolynomial ℂ q₀ * pullback q₀ p ≠ 0

/-- A real decoded decomposition exists with all amplitudes nonzero and the
same polynomial nonvanishing, in each prescribed exact-dimensional pattern. -/
def RealWitnessStatement : Prop :=
  ∀ (d : ℕ) (n : Fin d → ℕ) (r : ℕ) (_hd : 0 < d)
    (q₀ : Fin r → TensorIndex d n) (p : MvPolynomial (TensorIndex d n) ℂ)
    (A : Tensor ℂ d n) (a : Fin r → Tensor ℂ d n),
    Decomposes a A → MvPolynomial.eval (fun q => A q) p ≠ 0 →
      ∃ z : Parameter ℝ q₀,
        (∀ i, z ⟨i, none⟩ ≠ 0) ∧
        Decomposes (summands q₀ z) (sum q₀ z) ∧
        MvPolynomial.eval (fun q => complexify (sum q₀ z) q) p ≠ 0

#check DimensionStatement
#check EvaluationStatement
#check DecompositionStatement
#check RepresentationStatement
#check NonzeroPullbackStatement
#check RealWitnessStatement
end NLA.TR06.Segre
