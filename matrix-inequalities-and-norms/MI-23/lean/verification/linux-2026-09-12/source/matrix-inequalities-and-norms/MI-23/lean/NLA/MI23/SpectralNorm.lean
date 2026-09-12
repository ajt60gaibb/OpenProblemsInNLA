/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Exact characteristic-root and Euclidean operator-norm bridges for MI-23.
-/
import NLA.MI23.FunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Data.List.Pairwise

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI23

theorem orderedEigenvalues_multiset {n : ℕ} (A : Mat n) (hA : A.IsHermitian) :
    (↑(orderedEigenvalues A) : Multiset ℝ) = Finset.univ.val.map hA.eigenvalues := by
  simp only [orderedEigenvalues, Multiset.sort_eq]
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  congr 1

theorem largestEigenvalue_spec {n : ℕ} (A : Mat n) (hn : 1 ≤ n)
    (hA : HasOrderedPositiveEigenvalues A) :
    largestEigenvalue A ∈ orderedEigenvalues A ∧
      ∀ a ∈ orderedEigenvalues A, a ≤ largestEigenvalue A := by
  have hl := hA.1
  have hs := hA.2.1
  unfold largestEigenvalue
  cases he : orderedEigenvalues A with
  | nil => simp only [he, List.length_nil] at hl; omega
  | cons a l =>
    simp only [List.getD_cons_zero]
    refine ⟨List.mem_cons_self, ?_⟩
    intro b hb
    rw [he] at hs
    simpa only [List.head_cons] using hs.rel_head hb

theorem operatorNorm_eq_eigenvalueNorm {n : ℕ} (A : Mat n) (hA : A.IsHermitian) :
    operatorNorm A = ‖(fun i => (hA.eigenvalues i : ℂ))‖ := by
  change ‖A‖ = _
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  rfl

theorem largestEigenvalue_posDef_eq_norm {n : ℕ} (hn : 1 ≤ n)
    (A : Mat n) (hA : A.PosDef) : largestEigenvalue A = operatorNorm A := by
  have hsem := ordered_eigenvalues_posDef A hA
  obtain ⟨hmem, hmax⟩ := largestEigenvalue_spec A hn hsem
  have hm := orderedEigenvalues_multiset A hA.isHermitian
  have hpos : 0 < largestEigenvalue A := hsem.2.2.1 _ hmem
  have hentry : ∀ i, hA.isHermitian.eigenvalues i ∈ orderedEigenvalues A := by
    intro i
    change hA.isHermitian.eigenvalues i ∈ (↑(orderedEigenvalues A) : Multiset ℝ)
    rw [hm]
    exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val i, rfl⟩
  rw [operatorNorm_eq_eigenvalueNorm A hA.isHermitian]
  apply le_antisymm
  · have hh : largestEigenvalue A ∈ Finset.univ.val.map hA.isHermitian.eigenvalues := by
      rw [← hm]
      exact hmem
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hh
    rw [← hi]
    have hb := norm_le_pi_norm (fun j => (hA.isHermitian.eigenvalues j : ℂ)) i
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hA.eigenvalues_pos i)] using hb
  · apply (pi_norm_le_iff_of_nonneg hpos.le).mpr
    intro i
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hA.eigenvalues_pos i)]
      using hmax _ (hentry i)

theorem squared_product_largest_proved {n : ℕ} (hn : 1 ≤ n)
    (X Y : Mat n) (hX : X.PosDef) (hY : Y.PosDef) :
    largestEigenvalue (X ^ (2 : ℕ) * Y ^ (2 : ℕ)) = operatorNorm (X * Y) ^ 2 := by
  have hg : (Y * X ^ (2 : ℕ) * Y).PosDef :=
    sandwich_posDef _ Y (naturalPower_posDef X hX 2) hY
  have hc : (X ^ (2 : ℕ) * Y ^ (2 : ℕ)).charpoly =
      (Y * X ^ (2 : ℕ) * Y).charpoly := by
    calc
      _ = ((X ^ (2 : ℕ) * Y) * Y).charpoly := by simp only [pow_two, mul_assoc]
      _ = (Y * (X ^ (2 : ℕ) * Y)).charpoly := Matrix.charpoly_mul_comm _ _
      _ = _ := by rw [mul_assoc]
  have he : Y * X ^ (2 : ℕ) * Y = (X * Y)ᴴ * (X * Y) := by
    simp only [Matrix.conjTranspose_mul, hX.isHermitian.eq, hY.isHermitian.eq,
      pow_two, mul_assoc]
  rw [largestEigenvalue, orderedEigenvalues_congr hc]
  change largestEigenvalue (Y * X ^ (2 : ℕ) * Y) = _
  rw [largestEigenvalue_posDef_eq_norm hn _ hg, he]
  change ‖(X * Y)ᴴ * (X * Y)‖ = ‖X * Y‖ ^ 2
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, pow_two]

end NLA.MI23
