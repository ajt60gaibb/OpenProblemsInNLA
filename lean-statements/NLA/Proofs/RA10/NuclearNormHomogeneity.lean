import NLA.Proofs.RA10.NuclearIdealOperatorBridge
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! RA-10 exact scalar homogeneity of the frozen all-singular-value nuclear
norm. This proves only one generic ideal fact; the coefficient-one left/right
ideal inequalities and full RA-10 Target remain open. -/

set_option autoImplicit false
set_option leancert.trust "kernel"

open Polynomial
open scoped BigOperators

namespace NLA.Proofs.RA10

private theorem charpoly_smul_by_eigenbasis {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : T.IsSymmetric) (c : ℝ) :
    (c • T).charpoly =
      ∏ i : Fin n, (X - C (c * hT.eigenvalues (by simp) i)) := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  let b := (hT.eigenvectorBasis hn).toBasis
  have hmat : (c • T).toMatrix b b =
      Matrix.diagonal (fun i : Fin n => c * hT.eigenvalues hn i) := by
    ext i j
    simp [LinearMap.toMatrix_apply, b, Matrix.diagonal_apply,
      hT.apply_eigenvectorBasis, mul_comm]
    split_ifs with h <;> simp_all
  rw [← (c • T).charpoly_toMatrix b, hmat, Matrix.charpoly_diagonal]

#assert_trust kernel charpoly_smul_by_eigenbasis

private theorem eigenvalues_smul_nonneg {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : T.IsSymmetric) (c : ℝ) (hc : 0 ≤ c) :
    (show (c • T).IsSymmetric from hT.smul (by simp)).eigenvalues (by simp) =
      (fun i : Fin n => c * hT.eigenvalues (by simp) i) := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  have hcsym : (c • T).IsSymmetric := hT.smul (by simp)
  have hroots : (c • T).charpoly.roots =
      Multiset.map (fun i : Fin n => c * hT.eigenvalues hn i) Finset.univ.val := by
    rw [charpoly_smul_by_eigenbasis T hT c]
    rw [Polynomial.roots_prod _ _ (by
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      simpa only [← map_mul] using
        (Polynomial.X_sub_C_ne_zero (c * hT.eigenvalues hn i)))]
    simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  have hsorted : Antitone (fun i : Fin n => c * hT.eigenvalues hn i) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (hT.eigenvalues_antitone hn hij) hc
  rw [← List.ofFn_inj]
  calc
    List.ofFn (hcsym.eigenvalues hn) =
        ((c • T).charpoly.roots.map RCLike.re).sort (· ≥ ·) :=
      (hcsym.sort_roots_charpoly_eq_eigenvalues hn).symm
    _ = List.ofFn (fun i : Fin n => c * hT.eigenvalues hn i) := by
      rw [hroots]
      simp only [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
        Function.comp_def, Multiset.coe_sort]
      change (List.ofFn (fun i : Fin n => c * hT.eigenvalues hn i)).mergeSort
        (fun x₁ x₂ : ℝ => decide (x₁ ≥ x₂)) =
          List.ofFn (fun i : Fin n => c * hT.eigenvalues hn i)
      convert! List.mergeSort_of_pairwise ?_
      simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
      exact hsorted.sortedGE_ofFn

#assert_trust kernel eigenvalues_smul_nonneg

private theorem gram_smul {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (r : ℝ) :
    (r • T).adjoint ∘ₗ (r • T) =
      r ^ 2 • (T.adjoint ∘ₗ T) := by
  have hadj : (r • T).adjoint = r • T.adjoint := by
    change star (r • T) = r • star T
    simp
  ext x
  simp [hadj, LinearMap.comp_apply, pow_two, smul_smul]

#assert_trust kernel gram_smul

private theorem singularValues_smul_real {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (r : ℝ) (i : Fin n) :
    (r • T).singularValues i.val = |r| * T.singularValues i.val := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  rw [(r • T).singularValues_fin hn i, T.singularValues_fin hn i]
  simp only [gram_smul T r]
  have hpos : 0 ≤ r ^ 2 := sq_nonneg r
  have heig := congrFun
    (eigenvalues_smul_nonneg (T.adjoint ∘ₗ T)
      T.isSymmetric_adjoint_comp_self (r ^ 2) hpos) i
  rw [heig, Real.sqrt_mul hpos]
  simp [Real.sqrt_sq_eq_abs]

#assert_trust kernel singularValues_smul_real

theorem nuclearNorm_smul {n : ℕ} (r : ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.NuclearNorm (r • X) =
      |r| * NLA.Statements.RA10.NuclearNorm X := by
  unfold NLA.Statements.RA10.NuclearNorm
  rw [NLA.Proofs.RA10.toEuclideanLin_smul_exact]
  simp_rw [singularValues_smul_real]
  rw [Finset.mul_sum]

#assert_trust kernel nuclearNorm_smul
#print axioms nuclearNorm_smul

end NLA.Proofs.RA10
