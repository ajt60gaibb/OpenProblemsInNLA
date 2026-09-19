/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

Adapted from George Stepaniants's accepted MI22 Norms.lean and SingularValues.lean
at upstream commit e7519c46fd249a6a033bfe5d11c66bf47f7f8885. Those proofs in turn
credit the campaign's MI23 spectral/Frobenius norm bridges. Each result here is
re-proved on MI24's frozen definitions, without importing another solution.
The L2 matrix norm is explicitly identified with the actual Euclidean-map norm.
-/
import NLA.MI24.Definitions
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI24

lemma infinitySchattenNorm_eq_l2 {n : ℕ} (A : Mat n) :
    infinitySchattenNorm A = ‖A‖ :=
  Matrix.l2_opNorm_toEuclideanCLM A

lemma infinitySchattenNorm_nonneg {n : ℕ} (A : Mat n) :
    0 ≤ infinitySchattenNorm A := norm_nonneg _

lemma infinitySchattenNorm_eq_eigenvalueNorm {n : ℕ} (A : Mat n) (hA : A.IsHermitian) :
    infinitySchattenNorm A = ‖(fun i => (hA.eigenvalues i : ℂ))‖ := by
  rw [infinitySchattenNorm_eq_l2]
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  rfl

lemma infinitySchattenNorm_gram {n : ℕ} (A : Mat n) :
    infinitySchattenNorm (Aᴴ * A) = infinitySchattenNorm A ^ 2 := by
  simp only [infinitySchattenNorm_eq_l2, Matrix.l2_opNorm_conjTranspose_mul_self, pow_two]

theorem positive_infinity_monotone {n : ℕ} (hn : 1 ≤ n) (U V : Mat n)
    (hU : U.PosSemidef) (hV : V.PosSemidef) (hUV : U ≤ V) :
    infinitySchattenNorm U ≤ infinitySchattenNorm V := by
  simpa only [infinitySchattenNorm_eq_l2] using
    CStarAlgebra.norm_le_norm_of_nonneg_of_le hU.nonneg hUV

lemma infinitySchattenNorm_posSemidef_eq_first {n : ℕ} (hn : 1 ≤ n)
    (A : Mat n) (hA : A.PosSemidef) :
    infinitySchattenNorm A =
      hA.isHermitian.eigenvalues₀ ⟨0, by simpa using Nat.succ_le_iff.mp hn⟩ := by
  let i0 : Fin (Fintype.card (Fin n)) := ⟨0, by simpa using Nat.succ_le_iff.mp hn⟩
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have he (i) : hA.isHermitian.eigenvalues (e i) = hA.isHermitian.eigenvalues₀ i := by
    simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]
  have h0 : 0 ≤ hA.isHermitian.eigenvalues₀ i0 := by
    rw [← he]
    exact hA.eigenvalues_nonneg _
  rw [infinitySchattenNorm_eq_eigenvalueNorm A hA.isHermitian]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg h0).mpr
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)]
    -- View the natural inequality 0 ≤ index as the corresponding Fin
    -- order relation, which is the input expected by eigenvalues₀_antitone.
    exact hA.isHermitian.eigenvalues₀_antitone (show i0 ≤ e.symm i from Nat.zero_le _)
  · have hi := norm_le_pi_norm (fun i => (hA.isHermitian.eigenvalues i : ℂ)) (e i0)
    simpa only [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] using hi

lemma toEuclideanLin_gram {n : ℕ} (A : Mat n) :
    Matrix.toEuclideanLin (Aᴴ * A) =
      (Matrix.toEuclideanLin A).adjoint ∘ₗ Matrix.toEuclideanLin A := by
  rw [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

theorem infinity_schatten_semantics {n : ℕ} (hn : 1 ≤ n) (X : Mat n) :
    infinitySchattenNorm X = singularValue X 0 := by
  have hM := Matrix.posSemidef_conjTranspose_mul_self X
  have hnorm := infinitySchattenNorm_posSemidef_eq_first hn (Xᴴ * X) hM
  have hsq := (Matrix.toEuclideanLin X).sq_singularValues_of_lt
    (n := Fintype.card (Fin n)) finrank_euclideanSpace (i := 0)
    (by simpa using Nat.succ_le_iff.mp hn)
  have hgram : (Matrix.toEuclideanLin X).singularValues 0 ^ 2 =
      hM.isHermitian.eigenvalues₀ ⟨0, by simpa using Nat.succ_le_iff.mp hn⟩ := by
    rw [Matrix.IsHermitian.eigenvalues₀]
    simp only [toEuclideanLin_gram]
    exact hsq
  rw [infinitySchattenNorm_gram] at hnorm
  have hnon := (Matrix.toEuclideanLin X).singularValues_nonneg 0
  have hop := infinitySchattenNorm_nonneg X
  -- Expose singularValue as the singular value of toEuclideanLin X;
  -- the squared-norm identity and both nonnegativity facts use this API.
  change infinitySchattenNorm X = (Matrix.toEuclideanLin X).singularValues 0
  nlinarith

end NLA.MI24
