/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/recover_published_coverage.

Original MI27 resolution: Sidney Holden, Center for Computational Biology,
Flatiron Institute, Simons Foundation. This source reuses the actual two-basis
overlap lemmas of George Stepaniants's accepted MI24 TraceOverlap, authored
with Codex /root/nm04_final_referee1 and retaining its earlier MI22 credits.

UNCOMPILED helper source. No C16 theorem or matrix-log derivative is assumed.
The scalar tangent inequality is summed with the two different eigenbases'
nonnegative overlaps. Repeated eigenvalues require no exceptional treatment.
-/
import NLA.MI27.SpectralSemantics
import NLA.MI27.PositiveTrace
import NLA.MI24.TraceOverlap
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

/-- Actual trace of two finite functional calculi, using their distinct eigenbases. -/
lemma c16_trR_cfc_product {n : ℕ} (hn : 1 ≤ n) (X Y : Mat n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (f g : ℝ → ℝ) :
    trR (cfc f X * cfc g Y) =
      ∑ i : Fin n, ∑ j : Fin n,
        f (hX.eigenvalues i) * g (hY.eigenvalues j) *
          NLA.MI24.unitaryOverlapWeight
            (star hX.eigenvectorUnitary * hY.eigenvectorUnitary) i j := by
  rw [(spectral_function_semantics hn X hX f
      (X.finite_real_spectrum.continuousOn _)).1,
    (spectral_function_semantics hn Y hY g
      (Y.finite_real_spectrum.continuousOn _)).1]
  simpa only [trR, NLA.MI24.traceReal] using
    NLA.MI24.traceReal_two_conjugates hX.eigenvectorUnitary hY.eigenvectorUnitary
      (fun i => f (hX.eigenvalues i)) (fun j => g (hY.eigenvalues j))

lemma c16_trR_cfc_product_same {n : ℕ} (hn : 1 ≤ n) (X : Mat n)
    (hX : X.IsHermitian) (f g : ℝ → ℝ) :
    trR (cfc f X * cfc g X) =
      ∑ i : Fin n, f (hX.eigenvalues i) * g (hX.eigenvalues i) := by
  rw [← cfc_mul f g X (X.finite_real_spectrum.continuousOn _)
    (X.finite_real_spectrum.continuousOn _)]
  exact (spectral_function_semantics hn X hX (fun x => f x * g x)
    (X.finite_real_spectrum.continuousOn _)).2.1

lemma c16_trR_mul_log {n : ℕ} (hn : 1 ≤ n) (X : Mat n) (hX : X.IsHermitian) :
    trR (X * logM X) = ∑ i : Fin n, hX.eigenvalues i * Real.log (hX.eigenvalues i) := by
  simpa only [logM, CFC.log, cfc_id ℝ X hX.isSelfAdjoint, id_eq] using
    c16_trR_cfc_product_same hn X hX (id : ℝ → ℝ) Real.log

/-- Row normalization puts the linear increment in the same two-basis coordinates. -/
lemma c16_trR_cfc_mul_sub {n : ℕ} (hn : 1 ≤ n) (X Y : Mat n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (g : ℝ → ℝ) :
    trR (cfc g X * (Y - X)) =
      ∑ i : Fin n, ∑ j : Fin n,
        g (hX.eigenvalues i) * (hY.eigenvalues j - hX.eigenvalues i) *
          NLA.MI24.unitaryOverlapWeight
            (star hX.eigenvectorUnitary * hY.eigenvectorUnitary) i j := by
  have hxy := c16_trR_cfc_product hn X Y hX hY g (id : ℝ → ℝ)
  simp only [cfc_id ℝ Y hY.isSelfAdjoint, id_eq] at hxy
  have hxx := c16_trR_cfc_product_same hn X hX g (id : ℝ → ℝ)
  simp only [cfc_id ℝ X hX.isSelfAdjoint, id_eq] at hxx
  have hrow :
      (∑ i : Fin n, ∑ j : Fin n,
        g (hX.eigenvalues i) * hX.eigenvalues i *
          NLA.MI24.unitaryOverlapWeight
            (star hX.eigenvectorUnitary * hY.eigenvectorUnitary) i j) =
      ∑ i : Fin n, g (hX.eigenvalues i) * hX.eigenvalues i := by
    simp_rw [← Finset.mul_sum, NLA.MI24.unitaryOverlapWeight_row, mul_one]
  have hsub : trR (cfc g X * (Y - X)) =
      trR (cfc g X * Y) - trR (cfc g X * X) := by
    simp only [mul_sub, trR, Matrix.trace_sub, Complex.sub_re]
  rw [hsub, hxy, hxx, ← hrow]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]

/-- The scalar convex tangent bound, derived directly from log(u) ≤ u-1. -/
lemma c16_scalar_log_tangent (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x * Real.log x + (Real.log x + 1) * (y - x) ≤ y * Real.log y := by
  have hlog := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hx hy)) hy.le
  rw [Real.log_div hx.ne' hy.ne'] at hlog
  have hdiv : y * (x / y - 1) = x - y := by
    field_simp [hy.ne'] <;> ring
  rw [hdiv] at hlog
  nlinarith

/-- Only genuine unitary overlap weights are used; both marginals are proved in MI24. -/
lemma c16_weighted_log_tangent {n : ℕ} (U : unitary (Mat n))
    (x y : Fin n → ℝ) (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 < y j) :
    (∑ i : Fin n, x i * Real.log (x i)) +
      (∑ i : Fin n, ∑ j : Fin n,
        (Real.log (x i) + 1) * (y j - x i) *
          NLA.MI24.unitaryOverlapWeight U i j) ≤
      ∑ j : Fin n, y j * Real.log (y j) := by
  have hs :
      (∑ i : Fin n, ∑ j : Fin n,
        (x i * Real.log (x i) + (Real.log (x i) + 1) * (y j - x i)) *
          NLA.MI24.unitaryOverlapWeight U i j) ≤
      ∑ i : Fin n, ∑ j : Fin n,
        y j * Real.log (y j) * NLA.MI24.unitaryOverlapWeight U i j := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right (c16_scalar_log_tangent (x i) (y j) (hx i) (hy j))
      (NLA.MI24.unitaryOverlapWeight_nonneg U i j)
  have hrow :
      (∑ i : Fin n, ∑ j : Fin n,
        x i * Real.log (x i) * NLA.MI24.unitaryOverlapWeight U i j) =
      ∑ i : Fin n, x i * Real.log (x i) := by
    simp_rw [← Finset.mul_sum, NLA.MI24.unitaryOverlapWeight_row, mul_one]
  have hcol :
      (∑ i : Fin n, ∑ j : Fin n,
        y j * Real.log (y j) * NLA.MI24.unitaryOverlapWeight U i j) =
      ∑ j : Fin n, y j * Real.log (y j) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, NLA.MI24.unitaryOverlapWeight_column, mul_one]
  simp_rw [add_mul, Finset.sum_add_distrib] at hs
  rw [hrow, hcol] at hs
  simpa only [add_mul, Finset.sum_add_distrib] using hs

lemma c16_cfc_log_add_one {n : ℕ} (X : Mat n) (hX : X.IsHermitian) :
    cfc (fun x : ℝ => Real.log x + 1) X = logM X + (1 : Mat n) := by
  simpa only [logM, CFC.log, map_one] using
    cfc_add_const (1 : ℝ) Real.log X (X.finite_real_spectrum.continuousOn _)
      hX.isSelfAdjoint

/-- Trace Klein/tangent inequality, with no commutativity or spectral simplicity premise. -/
lemma c16_entropy_tangent {n : ℕ} (hn : 1 ≤ n) (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) :
    entropy Y - entropy X ≤ -trR ((logM X + 1) * (Y - X)) := by
  have hs := c16_weighted_log_tangent
    (star hX.isHermitian.eigenvectorUnitary * hY.isHermitian.eigenvectorUnitary)
    hX.isHermitian.eigenvalues hY.isHermitian.eigenvalues hX.eigenvalues_pos hY.eigenvalues_pos
  have hl := c16_trR_cfc_mul_sub hn X Y hX.isHermitian hY.isHermitian
    (fun x : ℝ => Real.log x + 1)
  rw [c16_cfc_log_add_one X hX.isHermitian] at hl
  simp only [entropy, c16_trR_mul_log hn X hX.isHermitian,
    c16_trR_mul_log hn Y hY.isHermitian, hl]
  linarith [hs]

/-- The entropy increment lies between its two endpoint trace tangents. -/
lemma c16_entropy_tangent_sandwich {n : ℕ} (hn : 1 ≤ n) (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) :
    -trR ((logM Y + 1) * (Y - X)) ≤ entropy Y - entropy X ∧
      entropy Y - entropy X ≤ -trR ((logM X + 1) * (Y - X)) := by
  refine ⟨?_, c16_entropy_tangent hn X Y hX hY⟩
  have hrev := c16_entropy_tangent hn Y X hY hX
  have hsign : trR ((logM Y + 1) * (X - Y)) =
      -trR ((logM Y + 1) * (Y - X)) := by
    simp only [mul_sub, trR, Matrix.trace_sub, Complex.sub_re]
    ring
  rw [hsign] at hrev
  linarith

#print axioms c16_entropy_tangent_sandwich

end NLA.MI27
