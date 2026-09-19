/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nr04_mf14_final_referee_a.

Original MI27 question: Audenaert and Kittaneh. Analytic resolution: Sidney
Holden, Flatiron Institute, Simons Foundation. The negative-count pencil
representation follows Peter E. Frenkel. Imported spectral code retains its
MI24/MI22 credits. The exact first three headers of PENCIL-INTEGRAL-STATEMENTS.md
were approved by root and independent referee B before proof development.
This source author runs no Lean or Comparator. No full C11 is claimed here.
-/
import NLA.MI27.PencilTraceLog
import NLA.MI27.PencilScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open MeasureTheory
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

lemma c11_posDef_normalizer {n : ℕ} (P : Mat n) (hP : P.PosDef) :
    ∃ S : Mat n, IsUnit S ∧ Sᴴ * P * S = 1 := by
  let S : Mat n := CFC.rpow P (-(1 / 2) : ℝ)
  have hS : IsStrictlyPositive S := IsStrictlyPositive.rpow P _ hP.isStrictlyPositive
  refine ⟨S, hS.isUnit, ?_⟩
  rw [hS.isSelfAdjoint.isHermitian.eq]
  exact CFC.conjugate_rpow_neg_one_half P hP.isStrictlyPositive

lemma c11_negativeCount_affine_identity_spectral {n : ℕ} (hn : 1 ≤ n)
    (C : Mat n) (hC : C.IsHermitian) (t : ℝ) :
    c11_negativeCount (1 + (t : ℂ) • C) =
      ∑ i : Fin n, if 1 + t * hC.eigenvalues i < 0 then (1 : ℝ) else 0 := by
  have haff : cfc (fun x : ℝ => 1 + t * x) C = 1 + (t : ℂ) • C := by
    rw [cfc_const_add 1 (fun x : ℝ => t * x) C
      (C.finite_real_spectrum.continuousOn _) hC.isSelfAdjoint,
      cfc_const_mul_id t C hC.isSelfAdjoint, map_one]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) t C]
    rfl
  have hc := cfc_comp' (fun x : ℝ => if x < 0 then (1 : ℝ) else 0)
    (fun x : ℝ => 1 + t * x) C
    ((C.finite_real_spectrum.image (fun x : ℝ => 1 + t * x)).continuousOn _)
    (C.finite_real_spectrum.continuousOn _) hC.isSelfAdjoint
  rw [haff] at hc
  unfold c11_negativeCount
  rw [← hc]
  exact (spectral_function_semantics hn C hC
    (fun x : ℝ => if 1 + t * x < 0 then (1 : ℝ) else 0)
    (C.finite_real_spectrum.continuousOn _)).2.1

lemma c11_normalized_pencil_count_integral {n : ℕ} (hn : 1 ≤ n)
    (C : Mat n) (hC : C.IsHermitian) (h1C : (1 + C).PosDef) :
    MeasureTheory.Integrable
      (fun t : ℝ => c11_pencilWeight t * c11_negativeCount (1 + (t : ℂ) • C)) ∧
      (∫ t : ℝ, c11_pencilWeight t * c11_negativeCount (1 + (t : ℂ) • C)) =
        trR (logM (1 + C)) - trR (C * (1 + C)⁻¹) := by
  obtain ⟨heig, htrace⟩ := c11_trace_log_resolvent_spectral hn C hC h1C
  have heq :
      (fun t : ℝ => c11_pencilWeight t * c11_negativeCount (1 + (t : ℂ) • C)) =
      fun t : ℝ => ∑ i : Fin n,
        c11_pencilWeight t * (if 1 + t * hC.eigenvalues i < 0 then (1 : ℝ) else 0) := by
    funext t
    rw [c11_negativeCount_affine_identity_spectral hn C hC, Finset.mul_sum]
  have hi (i : Fin n) : Integrable (fun t : ℝ =>
      c11_pencilWeight t * (if 1 + t * hC.eigenvalues i < 0 then (1 : ℝ) else 0)) :=
    (c11_scalar_pencil_count_integral (hC.eigenvalues i) (heig i)).1
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact integrable_finsetSum Finset.univ (fun i _ => hi i)
  · calc
      (∫ t : ℝ, c11_pencilWeight t * c11_negativeCount (1 + (t : ℂ) • C)) =
          ∑ i : Fin n, ∫ t : ℝ,
            c11_pencilWeight t * (if 1 + t * hC.eigenvalues i < 0 then (1 : ℝ) else 0) := by
        rw [heq]
        exact integral_finsetSum Finset.univ (fun i _ => hi i)
      _ = ∑ i : Fin n,
          (Real.log (1 + hC.eigenvalues i) - hC.eigenvalues i / (1 + hC.eigenvalues i)) :=
        Finset.sum_congr rfl (fun i _ =>
          (c11_scalar_pencil_count_integral (hC.eigenvalues i) (heig i)).2)
      _ = trR (logM (1 + C)) - trR (C * (1 + C)⁻¹) := htrace.symm

#print axioms c11_posDef_normalizer
#assert_trust kernel c11_posDef_normalizer
#print axioms c11_negativeCount_affine_identity_spectral
#assert_trust kernel c11_negativeCount_affine_identity_spectral
#print axioms c11_normalized_pencil_count_integral
#assert_trust kernel c11_normalized_pencil_count_integral

end NLA.MI27
