/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

The singular values here are Mathlib's complete ordered family on complex
Euclidean space. We connect its first value to the actual induced norm using
the sorted Hermitian eigenfamily and the adjoint-composition identity.
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
-/
import NLA.MI22.Norms

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI22

theorem operatorNorm_posSemidef_eq_first {n : ℕ} (hn : 1 ≤ n)
    (A : Mat n) (hA : A.PosSemidef) :
    operatorNorm A = hA.isHermitian.eigenvalues₀ ⟨0, by simpa using Nat.succ_le_iff.mp hn⟩ := by
  let i0 : Fin (Fintype.card (Fin n)) := ⟨0, by simpa using Nat.succ_le_iff.mp hn⟩
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have he (i) : hA.isHermitian.eigenvalues (e i) = hA.isHermitian.eigenvalues₀ i := by
    simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]
  have h0 : 0 ≤ hA.isHermitian.eigenvalues₀ i0 := by
    rw [← he]
    exact hA.eigenvalues_nonneg _
  rw [operatorNorm_eq_eigenvalueNorm A hA.isHermitian]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg h0).mpr
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hA.eigenvalues_nonneg i)]
    exact hA.isHermitian.eigenvalues₀_antitone
      (show i0 ≤ e.symm i from Nat.zero_le _)
  · have hi := norm_le_pi_norm (fun i => (hA.isHermitian.eigenvalues i : ℂ)) (e i0)
    simpa only [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] using hi

theorem toEuclideanLin_gram {n : ℕ} (A : Mat n) :
    Matrix.toEuclideanLin (Aᴴ * A) =
      (Matrix.toEuclideanLin A).adjoint ∘ₗ Matrix.toEuclideanLin A := by
  rw [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

theorem singularValue_zero_eq_operatorNorm {n : ℕ} (hn : 1 ≤ n) (A : Mat n) :
    singularValue A 0 = operatorNorm A := by
  have hM := Matrix.posSemidef_conjTranspose_mul_self A
  have hnorm := operatorNorm_posSemidef_eq_first hn (Aᴴ * A) hM
  have hsq := (Matrix.toEuclideanLin A).sq_singularValues_of_lt
    (n := Fintype.card (Fin n)) finrank_euclideanSpace (i := 0) (by simpa using Nat.succ_le_iff.mp hn)
  have hgram : (Matrix.toEuclideanLin A).singularValues 0 ^ 2 =
      hM.isHermitian.eigenvalues₀ ⟨0, by simpa using Nat.succ_le_iff.mp hn⟩ := by
    rw [Matrix.IsHermitian.eigenvalues₀]
    simp only [toEuclideanLin_gram]
    exact hsq
  rw [operatorNorm_gram] at hnorm
  have hnon := (Matrix.toEuclideanLin A).singularValues_nonneg 0
  have hop := operatorNorm_nonneg A
  change (Matrix.toEuclideanLin A).singularValues 0 = operatorNorm A
  nlinarith

theorem singular_values_semantics_proved {n : ℕ} (hn : 1 ≤ n) (A : Mat n) :
    (∀ j : ℕ, 0 ≤ singularValue A j) ∧
    Antitone (singularValue A) ∧
    (∀ j : ℕ, n ≤ j → singularValue A j = 0) ∧
    (∀ i : Fin n, singularValue A i =
      Real.sqrt ((Matrix.toEuclideanLin A).isSymmetric_adjoint_comp_self.eigenvalues
        (by simp) i)) ∧
    singularValue A 0 = operatorNorm A := by
  refine ⟨(Matrix.toEuclideanLin A).singularValues_nonneg,
    (Matrix.toEuclideanLin A).singularValues_antitone, ?_, ?_,
    singularValue_zero_eq_operatorNorm hn A⟩
  · intro j hj
    exact (Matrix.toEuclideanLin A).singularValues_of_finrank_le (by simpa using hj)
  · intro i
    exact (Matrix.toEuclideanLin A).singularValues_fin (by simp) i

end NLA.MI22
