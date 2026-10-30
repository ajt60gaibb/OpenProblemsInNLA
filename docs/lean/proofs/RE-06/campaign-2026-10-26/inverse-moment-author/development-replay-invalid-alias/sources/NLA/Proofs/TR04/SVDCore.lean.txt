import NLA.Computation.SVDMachine
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import LeanCert.Tactic.Verification

/-! Rectangular real SVD construction for the unchanged TR-04 machine model.
The spectral norm calculation follows the same Gram-operator argument used in
RA-10, with independent domain and codomain dimensions. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped InnerProductSpace BigOperators

namespace NLA.Proofs.TR04.SVD

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def rightBasis {m l : ℕ} (T : Space l →ₗ[ℝ] Space m) :
    OrthonormalBasis (Fin l) ℝ (Space l) :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis (by simp)

theorem norm_image_rightBasis {m l : ℕ} (T : Space l →ₗ[ℝ] Space m) (i : Fin l) :
    ‖T (rightBasis T i)‖ = T.singularValues i.val := by
  let G := T.adjoint ∘ₗ T
  let hG := T.isSymmetric_adjoint_comp_self
  have hn : Module.finrank ℝ (Space l) = l := by simp [Space]
  let b : OrthonormalBasis (Fin l) ℝ (Space l) := hG.eigenvectorBasis hn
  have hunit : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
  have heig : G (b i) = hG.eigenvalues hn i • b i := by
    simp [G, b, hG.apply_eigenvectorBasis]
  have hsq : ‖T (b i)‖ ^ 2 = hG.eigenvalues hn i := by
    rw [← real_inner_self_eq_norm_sq]
    calc
      ⟪T (b i), T (b i)⟫_ℝ = ⟪b i, G (b i)⟫_ℝ := by
        simpa [G, LinearMap.comp_apply] using
          (T.adjoint_inner_right (b i) (T (b i))).symm
      _ = ⟪b i, (hG.eigenvalues hn i) • b i⟫_ℝ := by rw [heig]
      _ = hG.eigenvalues hn i := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hunit]
        ring
  have hsig := T.sq_singularValues_fin hn i
  have hnonneg := T.singularValues_nonneg i.val
  have hnorm : 0 ≤ ‖T (b i)‖ := norm_nonneg _
  have hmain : ‖T (b i)‖ = T.singularValues i.val := by nlinarith
  simpa [b, hG, rightBasis] using hmain

theorem inner_image_rightBasis {m l : ℕ} (T : Space l →ₗ[ℝ] Space m)
    (i j : Fin l) (hij : i ≠ j) :
    ⟪T (rightBasis T i), T (rightBasis T j)⟫_ℝ = 0 := by
  calc
    ⟪T (rightBasis T i), T (rightBasis T j)⟫_ℝ =
        ⟪rightBasis T i, (T.adjoint ∘ₗ T) (rightBasis T j)⟫_ℝ := by
      simpa only [LinearMap.comp_apply] using
        (T.adjoint_inner_right (rightBasis T i) (T (rightBasis T j))).symm
    _ = ⟪rightBasis T i,
        T.isSymmetric_adjoint_comp_self.eigenvalues (by simp) j • rightBasis T j⟫_ℝ := by
      simp [rightBasis, T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis]
    _ = 0 := by rw [real_inner_smul_right, (rightBasis T).inner_eq_zero hij, mul_zero]

theorem image_rightBasis_eq_zero {m l : ℕ} (T : Space l →ₗ[ℝ] Space m)
    (i : Fin l) (hi : Module.finrank ℝ T.range ≤ i.val) :
    T (rightBasis T i) = 0 := by
  apply norm_eq_zero.mp
  rw [norm_image_rightBasis, T.singularValues_eq_zero_iff_le_finrank_range.mpr hi]

theorem range_finrank_le_domain {m l : ℕ} (T : Space l →ₗ[ℝ] Space m) :
    Module.finrank ℝ T.range ≤ l := by
  have h : Module.finrank ℝ T.range + Module.finrank ℝ T.ker = l := by
    simpa [Space] using T.finrank_range_add_finrank_ker
  omega

theorem range_finrank_le_codomain {m l : ℕ} (T : Space l →ₗ[ℝ] Space m) :
    Module.finrank ℝ T.range ≤ m := by
  simpa [Space] using T.range.finrank_le

def leftVector {m l : ℕ} (T : Space l →ₗ[ℝ] Space m) (i : Fin m) : Space m :=
  if h : i.val < l then
    (T.singularValues i.val)⁻¹ • T (rightBasis T ⟨i.val, h⟩)
  else 0

theorem orthonormal_leftVector_positive {m l : ℕ} (T : Space l →ₗ[ℝ] Space m) :
    Orthonormal ℝ ({i : Fin m | i.val < Module.finrank ℝ T.range}.domRestrict
      (leftVector T)) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hil : i.val.val < l := lt_of_lt_of_le i.property (range_finrank_le_domain T)
  have hjl : j.val.val < l := lt_of_lt_of_le j.property (range_finrank_le_domain T)
  have hsi : 0 < T.singularValues i.val.val :=
    T.singularValues_pos_iff_lt_finrank_range.mpr i.property
  by_cases hij : i = j
  · subst j
    simp only [Set.domRestrict_apply, leftVector, dif_pos hil, ite_true]
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
      norm_image_rightBasis]
    field_simp
  · have hij' : (⟨i.val.val, hil⟩ : Fin l) ≠ ⟨j.val.val, hjl⟩ := by
      intro h
      apply hij
      apply Subtype.ext
      exact Fin.ext (congrArg (fun k : Fin l => k.val) h)
    simp only [Set.domRestrict_apply, leftVector, dif_pos hil, dif_pos hjl, if_neg hij]
    rw [real_inner_smul_left, real_inner_smul_right, inner_image_rightBasis T _ _ hij']
    ring

theorem exists_leftBasis {m l : ℕ} (T : Space l →ₗ[ℝ] Space m) :
    ∃ u : OrthonormalBasis (Fin m) ℝ (Space m),
      ∀ i, i.val < Module.finrank ℝ T.range → u i = leftVector T i := by
  exact (orthonormal_leftVector_positive T).exists_orthonormalBasis_extension_of_card_eq
    (by simp [Space])

#assert_trust kernel norm_image_rightBasis
#assert_trust kernel inner_image_rightBasis
#assert_trust kernel image_rightBasis_eq_zero
#assert_trust kernel exists_leftBasis
#print axioms exists_leftBasis

end NLA.Proofs.TR04.SVD
