/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nr04_mf14_final_referee_a.

Original MI27 question: Audenaert and Kittaneh. Analytic resolution: Sidney
Holden, Flatiron Institute, Simons Foundation. Negative-count pencil route:
Peter E. Frenkel. The imported dimension/inertia proof is root-authored and
retains its own credits. All prior spectral/overlap authorship is retained.
This exact header was approved by root and independent referee B before
its body in PENCIL-INTEGRAL-STATEMENTS.md. The source author runs no Lean
or Comparator. No full C11 or completed original target is claimed here.
-/
import NLA.MI27.PencilCountBasic
import NLA.MI27.NegativeCountCongruence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open MeasureTheory
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

lemma c11_shifted_pencil_count_integral {n : ℕ} (hn : 1 ≤ n)
    (X Y : Mat n) (hX : X.PosDef) (hY : Y.PosDef) (r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.Integrable
      (fun t : ℝ => c11_pencilWeight t *
        c11_negativeCount (c11_identityShift (X + (t : ℂ) • (Y - X)) r)) ∧
      (∫ t : ℝ, c11_pencilWeight t *
        c11_negativeCount (c11_identityShift (X + (t : ℂ) • (Y - X)) r)) =
        c11_shiftKernel X Y hX.isHermitian hY.isHermitian r := by
  obtain ⟨S, hS, hSP⟩ :=
    c11_posDef_normalizer (c11_identityShift X r) (c11_identityShift_posDef X hX r hr)
  let C : Mat n := Sᴴ * (Y - X) * S
  have hC : C.IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul S (hY.isHermitian.sub hX.isHermitian)
  obtain ⟨h1C, hkernel⟩ := c11_normalized_pencil_trace_kernel hn X Y hX hY r hr S hS hSP
  have hnorm (t : ℝ) :
      Sᴴ * c11_identityShift (X + (t : ℂ) • (Y - X)) r * S = 1 + (t : ℂ) • C := by
    have hshift : c11_identityShift (X + (t : ℂ) • (Y - X)) r =
        c11_identityShift X r + (t : ℂ) • (Y - X) := by
      unfold c11_identityShift
      abel
    rw [hshift, mul_add, add_mul, hSP, mul_smul_comm, smul_mul_assoc]
  have hcount (t : ℝ) :
      c11_negativeCount (c11_identityShift (X + (t : ℂ) • (Y - X)) r) =
        c11_negativeCount (1 + (t : ℂ) • C) := by
    have ht : (c11_identityShift (X + (t : ℂ) • (Y - X)) r).IsHermitian :=
      (hX.isHermitian.add ((hY.isHermitian.sub hX.isHermitian).smul
        (by simp [IsSelfAdjoint]))).add
          (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint]))
    rw [← hnorm t]
    exact (c11_negativeCount_congruence hn _ S ht hS).symm
  have heq :
      (fun t : ℝ => c11_pencilWeight t *
        c11_negativeCount (c11_identityShift (X + (t : ℂ) • (Y - X)) r)) =
      fun t : ℝ => c11_pencilWeight t * c11_negativeCount (1 + (t : ℂ) • C) := by
    funext t
    rw [hcount]
  obtain ⟨hi, he⟩ := c11_normalized_pencil_count_integral hn C hC h1C
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hi
  · rw [heq, he]
    exact hkernel

#print axioms c11_shifted_pencil_count_integral
#assert_trust kernel c11_shifted_pencil_count_integral

end NLA.MI27
