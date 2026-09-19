/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nr04_mf14_final_referee_a.

Original MI27 question: Audenaert and Kittaneh. Analytic resolution: Sidney
Holden, Flatiron Institute, Simons Foundation. The pencil/identity-shift
route follows Peter E. Frenkel. The actual two-basis spectral and overlap
code retains its MI24/MI22 authorship. This source identifies a finite
spectral sum with the already established identity-shift derivative kernel.

These are the remaining three exact headers of TRACE-LOG-STATEMENTS.md,
approved by root and independent referee B before proof development. No
inertia, product-integral exchange, or full C11 conclusion is assumed here.
The source author runs no Lean or Comparator.
-/
import NLA.MI27.PencilTraceLogBasic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

lemma c11_shiftKernel_eq_trace_log_resolvent {n : ℕ} (hn : 1 ≤ n)
    (X Y : Mat n) (hX : X.PosDef) (hY : Y.PosDef) (r : ℝ) (hr : 0 ≤ r) :
    c11_shiftKernel X Y hX.isHermitian hY.isHermitian r =
      trR (logM (c11_identityShift Y r)) -
        trR (logM (c11_identityShift X r)) -
          trR ((Y - X) * (c11_identityShift Y r)⁻¹) := by
  let U : unitary (Mat n) :=
    star hX.isHermitian.eigenvectorUnitary * hY.isHermitian.eigenvectorUnitary
  have hYr := c11_identityShift_posDef Y hY r hr
  have hinv : (c11_identityShift Y r)⁻¹ =
      cfc (fun x : ℝ => (x + r)⁻¹) Y := by
    rw [c11_inv_eq_cfc _ hYr.isHermitian hYr.isUnit,
      c11_cfc_function_identityShift Y hY.isHermitian]
  have hlogX := (spectral_function_semantics hn X hX.isHermitian
    (fun x : ℝ => Real.log (x + r)) (X.finite_real_spectrum.continuousOn _)).2.1
  have hlogY := (spectral_function_semantics hn Y hY.isHermitian
    (fun x : ℝ => Real.log (x + r)) (Y.finite_real_spectrum.continuousOn _)).2.1
  have hself := c16_trR_cfc_product_same hn Y hY.isHermitian
    (id : ℝ → ℝ) (fun x : ℝ => (x + r)⁻¹)
  simp only [cfc_id ℝ Y hY.isHermitian.isSelfAdjoint, id_eq] at hself
  have hcross := c16_trR_cfc_product hn X Y hX.isHermitian hY.isHermitian
    (id : ℝ → ℝ) (fun x : ℝ => (x + r)⁻¹)
  simp only [cfc_id ℝ X hX.isHermitian.isSelfAdjoint, id_eq] at hcross
  have hcolinv :
      (∑ i : Fin n, ∑ j : Fin n,
        hY.isHermitian.eigenvalues j * (hY.isHermitian.eigenvalues j + r)⁻¹ *
          NLA.MI24.unitaryOverlapWeight U i j) =
      ∑ j : Fin n, hY.isHermitian.eigenvalues j * (hY.isHermitian.eigenvalues j + r)⁻¹ := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, NLA.MI24.unitaryOverlapWeight_column, mul_one]
  have hres : trR ((Y - X) * (c11_identityShift Y r)⁻¹) =
      ∑ i : Fin n, ∑ j : Fin n,
        (hY.isHermitian.eigenvalues j - hX.isHermitian.eigenvalues i) /
            (hY.isHermitian.eigenvalues j + r) *
          NLA.MI24.unitaryOverlapWeight U i j := by
    rw [hinv]
    have hsplit : trR ((Y - X) * cfc (fun x : ℝ => (x + r)⁻¹) Y) =
        trR (Y * cfc (fun x : ℝ => (x + r)⁻¹) Y) -
          trR (X * cfc (fun x : ℝ => (x + r)⁻¹) Y) := by
      simp only [sub_mul, trR, Matrix.trace_sub, Complex.sub_re]
    rw [hsplit, hself, hcross, ← hcolinv]
    simp only [U, div_eq_mul_inv, sub_mul, Finset.sum_sub_distrib]
  have hrowlog :
      (∑ i : Fin n, ∑ j : Fin n,
        Real.log (hX.isHermitian.eigenvalues i + r) *
          NLA.MI24.unitaryOverlapWeight U i j) =
      ∑ i : Fin n, Real.log (hX.isHermitian.eigenvalues i + r) := by
    simp_rw [← Finset.mul_sum, NLA.MI24.unitaryOverlapWeight_row, mul_one]
  have hcollog :
      (∑ i : Fin n, ∑ j : Fin n,
        Real.log (hY.isHermitian.eigenvalues j + r) *
          NLA.MI24.unitaryOverlapWeight U i j) =
      ∑ j : Fin n, Real.log (hY.isHermitian.eigenvalues j + r) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, NLA.MI24.unitaryOverlapWeight_column, mul_one]
  rw [c11_shiftKernel, c11_log_identityShift X hX.isHermitian,
    c11_log_identityShift Y hY.isHermitian, hlogX, hlogY, hres,
    ← hrowlog, ← hcollog]
  simp only [U, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

lemma c11_trace_log_resolvent_spectral {n : ℕ} (hn : 1 ≤ n)
    (C : Mat n) (hC : C.IsHermitian) (h1C : (1 + C).PosDef) :
    (∀ i : Fin n, -1 < hC.eigenvalues i) ∧
      trR (logM (1 + C)) - trR (C * (1 + C)⁻¹) =
        ∑ i : Fin n,
          (Real.log (1 + hC.eigenvalues i) -
            hC.eigenvalues i / (1 + hC.eigenvalues i)) := by
  have hshift : c11_identityShift C 1 = 1 + C := by
    simp [c11_identityShift, add_comm]
  have hcfc : cfc (fun x : ℝ => x + 1) C = 1 + C := by
    rw [c11_cfc_identityShift C hC, hshift]
  have hpos : ∀ x ∈ spectrum ℝ C, 0 < x + 1 := by
    apply (cfc_isStrictlyPositive_iff (fun x : ℝ => x + 1) C
      (C.finite_real_spectrum.continuousOn _) hC.isSelfAdjoint).mp
    rw [hcfc]
    exact h1C.isStrictlyPositive
  have heig : ∀ i : Fin n, -1 < hC.eigenvalues i := by
    intro i
    have hi : hC.eigenvalues i ∈ spectrum ℝ C := by
      rw [hC.spectrum_real_eq_range_eigenvalues]
      exact ⟨i, rfl⟩
    have := hpos (hC.eigenvalues i) hi
    linarith
  have hlog : logM (1 + C) = cfc (fun x : ℝ => Real.log (1 + x)) C := by
    rw [← hshift, c11_log_identityShift C hC]
    congr 1
    funext x
    rw [add_comm]
  have hinv : (1 + C)⁻¹ = cfc (fun x : ℝ => (1 + x)⁻¹) C := by
    calc
      (1 + C)⁻¹ = cfc (fun x : ℝ => x⁻¹) (1 + C) :=
        c11_inv_eq_cfc _ h1C.isHermitian h1C.isUnit
      _ = cfc (fun x : ℝ => x⁻¹) (c11_identityShift C 1) := by rw [hshift]
      _ = cfc (fun x : ℝ => (x + 1)⁻¹) C :=
        c11_cfc_function_identityShift C hC (fun x : ℝ => x⁻¹) 1
      _ = cfc (fun x : ℝ => (1 + x)⁻¹) C := by
        congr 1
        funext x
        rw [add_comm]
  have htr := (spectral_function_semantics hn C hC (fun x : ℝ => Real.log (1 + x))
    (C.finite_real_spectrum.continuousOn _)).2.1
  have hprod := c16_trR_cfc_product_same hn C hC (id : ℝ → ℝ)
    (fun x : ℝ => (1 + x)⁻¹)
  simp only [cfc_id ℝ C hC.isSelfAdjoint, id_eq] at hprod
  refine ⟨heig, ?_⟩
  rw [hlog, hinv, htr, hprod]
  simp only [Finset.sum_sub_distrib, div_eq_mul_inv]

lemma c11_normalized_pencil_trace_kernel {n : ℕ} (hn : 1 ≤ n)
    (X Y : Mat n) (hX : X.PosDef) (hY : Y.PosDef) (r : ℝ) (hr : 0 ≤ r)
    (S : Mat n) (hS : IsUnit S)
    (hSP : Sᴴ * c11_identityShift X r * S = 1) :
    (1 + Sᴴ * (Y - X) * S).PosDef ∧
      trR (logM (1 + Sᴴ * (Y - X) * S)) -
          trR ((Sᴴ * (Y - X) * S) * (1 + Sᴴ * (Y - X) * S)⁻¹) =
        c11_shiftKernel X Y hX.isHermitian hY.isHermitian r := by
  have hP := c11_identityShift_posDef X hX r hr
  have hQ := c11_identityShift_posDef Y hY r hr
  have hPQ : c11_identityShift Y r = c11_identityShift X r + (Y - X) := by
    unfold c11_identityShift
    abel
  have hN : 1 + Sᴴ * (Y - X) * S = Sᴴ * c11_identityShift Y r * S := by
    rw [hPQ, mul_add, add_mul, hSP]
  refine ⟨?_, ?_⟩
  · rw [hN]
    exact hQ.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hS)
  · rw [hN, c11_trR_log_normalized_congruence hn _ _ S hP hQ hS hSP,
      c11_trR_congruence_mul_inv _ _ S hQ.isUnit hS,
      c11_shiftKernel_eq_trace_log_resolvent hn X Y hX hY r hr]

#print axioms c11_shiftKernel_eq_trace_log_resolvent
#assert_trust kernel c11_shiftKernel_eq_trace_log_resolvent
#print axioms c11_trace_log_resolvent_spectral
#assert_trust kernel c11_trace_log_resolvent_spectral
#print axioms c11_normalized_pencil_trace_kernel
#assert_trust kernel c11_normalized_pencil_trace_kernel

end NLA.MI27
