/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

Finite scalar Holder is applied on pairs of eigenvector indices, splitting each
overlap weight into its reciprocal-exponent powers. Both zero weights and zero
eigenvalues are covered by nonnegative-power identities. No normalization divides
by a Schatten norm, so singular and zero matrices need no positivity shortcut.
-/
import NLA.MI24.TraceOverlap
import NLA.MI24.PowerScaling
import Mathlib.Analysis.MeanInequalities

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section
namespace NLA.MI24

lemma unitaryOverlapWeight_holder {n : ℕ} (U : unitary (Mat n))
    (x y : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j)
    (p q : ℝ) (hpq : p.HolderConjugate q) :
    (∑ i : Fin n, ∑ j : Fin n, x i * y j * unitaryOverlapWeight U i j) ≤
      (∑ i : Fin n, x i ^ p) ^ (1 / p) * (∑ j : Fin n, y j ^ q) ^ (1 / q) := by
  let F : Fin n × Fin n → ℝ := fun ij =>
    x ij.1 * unitaryOverlapWeight U ij.1 ij.2 ^ p⁻¹
  let G : Fin n × Fin n → ℝ := fun ij =>
    y ij.2 * unitaryOverlapWeight U ij.1 ij.2 ^ q⁻¹
  have hF (ij : Fin n × Fin n) : 0 ≤ F ij :=
    mul_nonneg (hx _) (Real.rpow_nonneg (unitaryOverlapWeight_nonneg U _ _) _)
  have hG (ij : Fin n × Fin n) : 0 ≤ G ij :=
    mul_nonneg (hy _) (Real.rpow_nonneg (unitaryOverlapWeight_nonneg U _ _) _)
  have hFpow (i j : Fin n) : F (i, j) ^ p = x i ^ p * unitaryOverlapWeight U i j := by
    dsimp only [F]
    rw [Real.mul_rpow (hx i) (Real.rpow_nonneg (unitaryOverlapWeight_nonneg U i j) _),
      Real.rpow_inv_rpow (unitaryOverlapWeight_nonneg U i j) hpq.ne_zero]
  have hGpow (i j : Fin n) : G (i, j) ^ q = y j ^ q * unitaryOverlapWeight U i j := by
    dsimp only [G]
    rw [Real.mul_rpow (hy j) (Real.rpow_nonneg (unitaryOverlapWeight_nonneg U i j) _),
      Real.rpow_inv_rpow (unitaryOverlapWeight_nonneg U i j) hpq.symm.ne_zero]
  have hFsum : (∑ ij : Fin n × Fin n, F ij ^ p) = ∑ i : Fin n, x i ^ p := by
    rw [Fintype.sum_prod_type]
    simp_rw [hFpow, ← Finset.mul_sum, unitaryOverlapWeight_row, mul_one]
  have hGsum : (∑ ij : Fin n × Fin n, G ij ^ q) = ∑ j : Fin n, y j ^ q := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [hGpow, ← Finset.mul_sum, unitaryOverlapWeight_column, mul_one]
  have hprod (i j : Fin n) :
      F (i, j) * G (i, j) = x i * y j * unitaryOverlapWeight U i j := by
    calc
      _ = x i * y j *
          (unitaryOverlapWeight U i j ^ p⁻¹ * unitaryOverlapWeight U i j ^ q⁻¹) := by
        dsimp only [F, G]
        ring
      _ = _ := by
        rw [← Real.rpow_add_of_nonneg (unitaryOverlapWeight_nonneg U i j)
          hpq.inv_nonneg hpq.symm.inv_nonneg, hpq.inv_add_inv_eq_one, Real.rpow_one]
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ) (f := F) (g := G)
    hpq (fun ij _ => hF ij) (fun ij _ => hG ij)
  rw [hFsum, hGsum] at h
  simpa only [Fintype.sum_prod_type, hprod] using h

lemma traceReal_mul_nonneg {n : ℕ} (A B : Mat n)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ traceReal (A * B) := by
  have haone : spectralPower A 1 = A := CFC.rpow_one A hA.nonneg
  have hbone : spectralPower B 1 = B := CFC.rpow_one B hB.nonneg
  have ht := traceReal_spectralPower_product A B hA hB 1 1
  rw [haone, hbone] at ht
  simp only [Real.rpow_one] at ht
  rw [ht]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (hA.eigenvalues_nonneg i) (hB.eigenvalues_nonneg j))
      (unitaryOverlapWeight_nonneg _ i j)

lemma traceReal_mul_order {n : ℕ} (A B D : Mat n)
    (hAB : A ≤ B) (hD : D.PosSemidef) : traceReal (A * D) ≤ traceReal (B * D) := by
  have h := traceReal_mul_nonneg (B - A) D
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hAB)) hD
  simpa only [sub_mul, traceReal, Matrix.trace_sub, Complex.sub_re, sub_nonneg] using h

lemma positive_trace_holder {n : ℕ} (A B : Mat n)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (p q : ℝ) (hpq : p.HolderConjugate q) :
    traceReal (A * B) ≤ finiteSchattenNorm p A * finiteSchattenNorm q B := by
  have haone : spectralPower A 1 = A := CFC.rpow_one A hA.nonneg
  have hbone : spectralPower B 1 = B := CFC.rpow_one B hB.nonneg
  calc
    _ = traceReal (spectralPower A 1 * spectralPower B 1) := by rw [haone, hbone]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        hA.isHermitian.eigenvalues i * hB.isHermitian.eigenvalues j *
          unitaryOverlapWeight
            (star hA.isHermitian.eigenvectorUnitary * hB.isHermitian.eigenvectorUnitary) i j := by
      rw [traceReal_spectralPower_product A B hA hB]
      simp only [Real.rpow_one]
    _ ≤ (∑ i : Fin n, hA.isHermitian.eigenvalues i ^ p) ^ (1 / p) *
        (∑ j : Fin n, hB.isHermitian.eigenvalues j ^ q) ^ (1 / q) :=
      unitaryOverlapWeight_holder _ _ _ hA.eigenvalues_nonneg hB.eigenvalues_nonneg p q hpq
    _ = _ := by
      rw [finiteSchattenNorm_of_posSemidef A hA, finiteSchattenNorm_of_posSemidef B hB,
        traceReal_spectralPower A hA, traceReal_spectralPower B hB]

end NLA.MI24
