import Mathlib

/-!
A finite graph-matrix model with one injective map per shape block.  We
use ordered representative edges and a symmetric sign function; this avoids
choosing orientations of unordered graph edges.  This file proves a general
two-block trace expansion.  It does not impose the paper's admissible-shape
classification or count parity-even intersection patterns.
-/

namespace MD01GraphMatrix

structure Shape where
  k : ℕ
  u : Fin k
  v : Fin k
  edges : Finset (Fin k × Fin k)

variable {n : ℕ}

def weight (τ : Shape) (σ : Fin n → Fin n → ℤ)
    (f : Fin τ.k ↪ Fin n) : ℤ :=
  ∏ e ∈ τ.edges, σ (f e.1) (f e.2)

noncomputable def graphMatrix (τ : Shape) (σ : Fin n → Fin n → ℤ) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun a b => ∑ f : Fin τ.k ↪ Fin n,
    if f τ.u = a ∧ f τ.v = b then weight τ σ f else 0

theorem trace_two_expand (τ ρ : Shape) (σ : Fin n → Fin n → ℤ) :
    Matrix.trace (graphMatrix τ σ * graphMatrix ρ σ) =
      ∑ a : Fin n, ∑ b : Fin n,
        ∑ f : Fin τ.k ↪ Fin n, ∑ g : Fin ρ.k ↪ Fin n,
          if f τ.u = a ∧ f τ.v = b ∧ g ρ.u = b ∧ g ρ.v = a then
            weight τ σ f * weight ρ σ g else 0 := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, graphMatrix]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro g hg
  by_cases hfg : f τ.u = a ∧ f τ.v = b
  · by_cases hga : g ρ.u = b ∧ g ρ.v = a <;> simp [hfg, hga]
  · by_cases hga : g ρ.u = b ∧ g ρ.v = a <;> simp [hfg, hga]

/-- A four-block cyclic trace expansion, prior to expanding the individual
graph-matrix blocks into injective labelings. -/
theorem trace_four_matrices (A B C D : Matrix (Fin n) (Fin n) ℤ) :
    Matrix.trace (((A * B) * C) * D) =
      ∑ a : Fin n, ∑ d : Fin n, ∑ c : Fin n, ∑ b : Fin n,
        ((A a b * B b c) * C c d) * D d a := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Finset.sum_mul]

/-- The four-block trace expanded into independent injective maps for
each block, with cyclic boundary compatibility left as explicit tests. -/
theorem trace_four_graph_expand (τ₁ τ₂ τ₃ τ₄ : Shape)
    (σ : Fin n → Fin n → ℤ) :
    Matrix.trace (((graphMatrix τ₁ σ * graphMatrix τ₂ σ) *
      graphMatrix τ₃ σ) * graphMatrix τ₄ σ) =
    ∑ a : Fin n, ∑ d : Fin n, ∑ c : Fin n, ∑ b : Fin n,
      ∑ f₄ : Fin τ₄.k ↪ Fin n,
      ∑ f₃ : Fin τ₃.k ↪ Fin n,
      ∑ f₂ : Fin τ₂.k ↪ Fin n,
      ∑ f₁ : Fin τ₁.k ↪ Fin n,
        (((if f₁ τ₁.u = a ∧ f₁ τ₁.v = b then weight τ₁ σ f₁ else 0) *
          (if f₂ τ₂.u = b ∧ f₂ τ₂.v = c then weight τ₂ σ f₂ else 0)) *
          (if f₃ τ₃.u = c ∧ f₃ τ₃.v = d then weight τ₃ σ f₃ else 0)) *
          (if f₄ τ₄.u = d ∧ f₄ τ₄.v = a then weight τ₄ σ f₄ else 0) := by
  classical
  rw [trace_four_matrices]
  simp only [graphMatrix]
  simp only [Finset.sum_mul, Finset.mul_sum]

#print axioms trace_two_expand
#print axioms trace_four_matrices
#print axioms trace_four_graph_expand

end MD01GraphMatrix
