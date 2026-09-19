/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nr04_mf14_final_referee_a.

Original MI27 question: Audenaert and Kittaneh. Analytic resolution: Sidney
Holden, Flatiron Institute, Simons Foundation. This partial C11 development
uses the identity-shift integral method of Peter E. Frenkel and Mathlib's
actual finite Hermitian CFC. The retained MI24/MI22 spectral and trace bridge
credits remain in the imported modules.

This small shared module defines the literal strict negative spectral count.
Zero eigenvalues are excluded; all multiplicities are retained. No inertia,
pencil integral, or full C11 conclusion is assumed or claimed here.
The definitions and exact headers were approved before implementation in
NEGATIVE-COUNT-LAYERCAKE-STATEMENTS.md.
-/
import NLA.MI27.IdentityShift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

/-- The real trace of the actual strict negative spectral projection. -/
def c11_negativeCount {n : ℕ} (M : Mat n) : ℝ :=
  trR (cfc (fun x : ℝ => if x < 0 then 1 else 0) M)

/-- Every scalar function is continuous on a finite spectrum, including the step function. -/
lemma c11_cfc_function_identityShift {n : ℕ} (M : Mat n)
    (hM : M.IsHermitian) (f : ℝ → ℝ) (r : ℝ) :
    cfc f (c11_identityShift M r) = cfc (fun x : ℝ => f (x + r)) M := by
  have hc := cfc_comp' f (fun x : ℝ => x + r) M
    ((M.finite_real_spectrum.image (fun x : ℝ => x + r)).continuousOn _)
    (M.finite_real_spectrum.continuousOn _) hM.isSelfAdjoint
  rw [c11_cfc_identityShift M hM r] at hc
  exact hc.symm

lemma c11_negativeCount_spectral {n : ℕ} (hn : 1 ≤ n) (M : Mat n)
    (hM : M.IsHermitian) :
    c11_negativeCount M =
      ∑ i : Fin n, if hM.eigenvalues i < 0 then (1 : ℝ) else 0 := by
  exact (spectral_function_semantics hn M hM
    (fun x : ℝ => if x < 0 then 1 else 0)
    (M.finite_real_spectrum.continuousOn _)).2.1

lemma c11_negativeCount_bounds {n : ℕ} (hn : 1 ≤ n) (M : Mat n)
    (hM : M.IsHermitian) :
    0 ≤ c11_negativeCount M ∧ c11_negativeCount M ≤ (n : ℝ) := by
  rw [c11_negativeCount_spectral hn M hM]
  refine ⟨Finset.sum_nonneg (fun i _ => ?_), ?_⟩
  · split_ifs <;> norm_num
  · calc
      (∑ i : Fin n, if hM.eigenvalues i < 0 then (1 : ℝ) else 0) ≤
          ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs <;> norm_num
      _ = (n : ℝ) := by simp

lemma c11_negativeCount_identityShift {n : ℕ} (hn : 1 ≤ n) (M : Mat n)
    (hM : M.IsHermitian) (r : ℝ) :
    c11_negativeCount (c11_identityShift M r) =
      ∑ i : Fin n, if hM.eigenvalues i + r < 0 then (1 : ℝ) else 0 := by
  unfold c11_negativeCount
  rw [c11_cfc_function_identityShift M hM]
  exact (spectral_function_semantics hn M hM
    (fun x : ℝ => if x + r < 0 then 1 else 0)
    (M.finite_real_spectrum.continuousOn _)).2.1

lemma c11_tracePos_neg_identityShift {n : ℕ} (hn : 1 ≤ n) (M : Mat n)
    (hM : M.IsHermitian) (r : ℝ) :
    tracePos (-(c11_identityShift M r)) =
      ∑ i : Fin n, max (-(hM.eigenvalues i + r)) 0 := by
  have hs : (c11_identityShift M r).IsHermitian :=
    hM.add (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint]))
  have hneg : cfc (fun x : ℝ => max x 0) (-(c11_identityShift M r)) =
      cfc (fun x : ℝ => max (-x) 0) (c11_identityShift M r) :=
    (cfc_comp_neg (f := fun x : ℝ => max x 0) (a := c11_identityShift M r)
      (((c11_identityShift M r).finite_real_spectrum.image (fun x : ℝ => -x)).continuousOn _)
      hs.isSelfAdjoint).symm
  change trR (cfc (fun x : ℝ => max x 0) (-(c11_identityShift M r))) = _
  rw [hneg, c11_cfc_function_identityShift M hM]
  exact (spectral_function_semantics hn M hM
    (fun x : ℝ => max (-(x + r)) 0)
    (M.finite_real_spectrum.continuousOn _)).2.1

#print axioms c11_cfc_function_identityShift
#print axioms c11_negativeCount_spectral
#print axioms c11_negativeCount_bounds
#print axioms c11_negativeCount_identityShift
#print axioms c11_tracePos_neg_identityShift

end NLA.MI27
