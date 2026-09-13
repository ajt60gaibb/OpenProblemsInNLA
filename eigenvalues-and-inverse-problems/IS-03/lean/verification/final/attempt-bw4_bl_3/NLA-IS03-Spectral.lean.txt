/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

An eigenbasis is derived from the proved separability of the concrete polynomial.
No diagonalizability assumption is imposed on a possible realizing matrix.
-/
import NLA.IS03.Algebra
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
open Matrix Polynomial
open scoped Classical
namespace NLA.IS03

abbrev ComplexRoots := derivativePolynomial.rootSet ℂ

theorem complexRoots_card : Fintype.card ComplexRoots = 6 := by
  rw [Polynomial.card_rootSet_eq_natDegree derivativePolynomial_separable
    (IsAlgClosed.splits _), derivativePolynomial_degree]

/-- Every proposed realization yields a genuine eigenbasis indexed by all six roots. -/
theorem exists_root_eigenbasis (B : RealMatrix 6)
    (hB : B.charpoly = derivativePolynomial) :
    ∃ b : Module.Basis ComplexRoots ℂ (Fin 6 → ℂ),
      ∀ r : ComplexRoots,
        Module.End.HasEigenvector (B.map (algebraMap ℝ ℂ)).toLin' (r : ℂ) (b r) := by
  let f : Module.End ℂ (Fin 6 → ℂ) := (B.map (algebraMap ℝ ℂ)).toLin'
  have hchar : f.charpoly = derivativePolynomial.map (algebraMap ℝ ℂ) := by
    change (B.map (algebraMap ℝ ℂ)).toLin'.charpoly = _
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map, hB]
  have he : ∀ r : ComplexRoots, f.HasEigenvalue (r : ℂ) := by
    intro r
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hchar]
    rw [Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
    exact Polynomial.aeval_eq_zero_of_mem_rootSet r.property
  choose v hv using fun r => (he r).exists_hasEigenvector
  have hlin : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' f (fun r : ComplexRoots => (r : ℂ))
      Subtype.coe_injective v hv
  have hcard : Fintype.card ComplexRoots = Module.finrank ℂ (Fin 6 → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact complexRoots_card
  let b := basisOfLinearIndependentOfCardEqFinrank' v hlin hcard
  refine ⟨b, ?_⟩
  intro r
  change f.HasEigenvector (r : ℂ) (b r)
  simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank'] using hv r

/-- A basis of eigenvectors identifies actual matrix powers, traces, and characteristic factors. -/
theorem root_product_and_trace (B : RealMatrix 6)
    (hB : B.charpoly = derivativePolynomial) :
    (∏ r : ComplexRoots, (X - C (r : ℂ))) =
        derivativePolynomial.map (algebraMap ℝ ℂ) ∧
    ∀ k : ℕ, ((Matrix.trace (B^k) : ℝ) : ℂ) = ∑ r : ComplexRoots, (r : ℂ)^k := by
  obtain ⟨b, hb⟩ := exists_root_eigenbasis B hB
  let M := B.map (algebraMap ℝ ℂ)
  let f : Module.End ℂ (Fin 6 → ℂ) := M.toLin'
  have hdiag (k : ℕ) : LinearMap.toMatrix b b (f^k) =
      Matrix.diagonal (fun r : ComplexRoots => (r : ℂ)^k) := by
    ext i j
    rw [LinearMap.toMatrix_apply, (hb j).pow_apply]
    by_cases h : i = j
    · subst j
      simp
    · simp [h]
  constructor
  · calc
      (∏ r : ComplexRoots, (X - C (r : ℂ))) =
          (Matrix.diagonal (fun r : ComplexRoots => (r : ℂ))).charpoly :=
        (Matrix.charpoly_diagonal _).symm
      _ = (LinearMap.toMatrix b b f).charpoly := by simpa using congrArg Matrix.charpoly (hdiag 1).symm
      _ = f.charpoly := LinearMap.charpoly_toMatrix _ _
      _ = derivativePolynomial.map (algebraMap ℝ ℂ) := by
        change (B.map (algebraMap ℝ ℂ)).toLin'.charpoly = _
        rw [Matrix.charpoly_toLin', Matrix.charpoly_map, hB]
  · intro k
    calc
      ((Matrix.trace (B^k) : ℝ) : ℂ) = Matrix.trace (M^k) := by
        change (algebraMap ℝ ℂ) (Matrix.trace (B^k)) = _
        rw [AddMonoidHom.map_trace, Matrix.map_pow]
      _ = LinearMap.trace ℂ (Fin 6 → ℂ) (f^k) := by
        rw [← Matrix.toLin'_pow, Matrix.trace_toLin'_eq]
      _ = Matrix.trace (LinearMap.toMatrix b b (f^k)) := LinearMap.trace_eq_matrix_trace ℂ b _
      _ = ∑ r : ComplexRoots, (r : ℂ)^k := by rw [hdiag, Matrix.trace_diagonal]

end NLA.IS03
