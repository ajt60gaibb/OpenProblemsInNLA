/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nr04_mf14_final_referee_a.

Original MI27 question: Audenaert and Kittaneh. Analytic resolution: Sidney
Holden, Flatiron Institute, Simons Foundation. The pencil/identity-shift
route follows Peter E. Frenkel. Imported MI24/MI22 spectral code retains
its prior authorship. These elementary matrix trace identities use pinned
Mathlib's Hermitian spectral theorem and nonsingular inverse.

The five exact headers here are the first five of TRACE-LOG-STATEMENTS.md,
approved by root and independent referee B before any bodies. In particular,
the logarithm identity is an identity of traces, not of conjugated matrices.
The source author runs no Lean or Comparator. Full C11 is not claimed here.
-/
import NLA.MI27.IdentityShiftFTC
import NLA.MI27.NegativeCount
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

lemma c11_identityShift_posDef {n : ℕ} (X : Mat n) (hX : X.PosDef)
    (r : ℝ) (hr : 0 ≤ r) :
    (c11_identityShift X r).PosDef := by
  change (X + (r : ℂ) • (1 : Mat n)).PosDef
  apply hX.add_posSemidef
  have hrc : (0 : ℂ) ≤ (r : ℂ) := by exact_mod_cast hr
  exact Matrix.PosSemidef.one.smul hrc

lemma c11_inv_eq_cfc {n : ℕ} (M : Mat n) (hM : M.IsHermitian)
    (hunit : IsUnit M) :
    M⁻¹ = cfc (fun x : ℝ => x⁻¹) M := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  exact (cfc_ringInverse_id (R := ℝ) M hunit hM.isSelfAdjoint).symm

lemma c11_trR_log_eq_log_det {n : ℕ} (hn : 1 ≤ n) (P : Mat n)
    (hP : P.PosDef) :
    trR (logM P) = Real.log (Matrix.det P).re := by
  have htr := (spectral_function_semantics hn P hP.isHermitian Real.log
    (P.finite_real_spectrum.continuousOn _)).2.1
  have hdet : Matrix.det P = ((∏ i : Fin n, hP.isHermitian.eigenvalues i : ℝ) : ℂ) := by
    rw [hP.isHermitian.det_eq_prod_eigenvalues]
    exact (RCLike.ofReal_prod Finset.univ hP.isHermitian.eigenvalues).symm
  rw [logM, CFC.log, htr, hdet, Complex.ofReal_re]
  exact (Real.log_prod (fun i _ => (hP.eigenvalues_pos i).ne')).symm

lemma c11_trR_log_normalized_congruence {n : ℕ} (hn : 1 ≤ n)
    (P Q S : Mat n) (hP : P.PosDef) (hQ : Q.PosDef) (hS : IsUnit S)
    (hSP : Sᴴ * P * S = 1) :
    trR (logM (Sᴴ * Q * S)) = trR (logM Q) - trR (logM P) := by
  have hN : (Sᴴ * Q * S).PosDef :=
    hQ.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hS)
  have hnorm := congrArg Matrix.det hSP
  simp only [Matrix.det_mul, Matrix.det_one] at hnorm
  have hprod : Matrix.det (Sᴴ * Q * S) * Matrix.det P = Matrix.det Q := by
    simp only [Matrix.det_mul]
    calc
      (Matrix.det Sᴴ * Matrix.det Q * Matrix.det S) * Matrix.det P =
          (Matrix.det Sᴴ * Matrix.det P * Matrix.det S) * Matrix.det Q := by ring
      _ = Matrix.det Q := by rw [hnorm, one_mul]
  have hquot : Matrix.det (Sᴴ * Q * S) = Matrix.det Q / Matrix.det P :=
    (eq_div_iff hP.det_pos.ne').2 hprod
  have hPr : 0 < (Matrix.det P).re := (Complex.pos_iff.mp hP.det_pos).1
  have hQr : 0 < (Matrix.det Q).re := (Complex.pos_iff.mp hQ.det_pos).1
  have hPi : (Matrix.det P).im = 0 := (Complex.pos_iff.mp hP.det_pos).2.symm
  have hPcast : Matrix.det P = ((Matrix.det P).re : ℂ) := by
    apply Complex.ext <;> simp [hPi]
  rw [hPcast] at hquot
  have hre : (Matrix.det (Sᴴ * Q * S)).re =
      (Matrix.det Q).re / (Matrix.det P).re := by
    simpa only [Complex.div_ofReal_re] using congrArg Complex.re hquot
  rw [c11_trR_log_eq_log_det hn _ hN, c11_trR_log_eq_log_det hn _ hQ,
    c11_trR_log_eq_log_det hn _ hP, hre, Real.log_div hQr.ne' hPr.ne']

lemma c11_trR_congruence_mul_inv {n : ℕ} (A B S : Mat n)
    (hB : IsUnit B) (hS : IsUnit S) :
    trR ((Sᴴ * A * S) * (Sᴴ * B * S)⁻¹) = trR (A * B⁻¹) := by
  letI := hS.invertible
  letI := hB.invertible
  have hSH : IsUnit Sᴴ := by simpa only [Matrix.star_eq_conjTranspose] using hS.star
  letI := hSH.invertible
  have he : (Sᴴ * A * S) * (Sᴴ * B * S)⁻¹ =
      Sᴴ * (A * B⁻¹) * (Sᴴ)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [← mul_assoc, Matrix.mul_inv_cancel_right_of_invertible]
  unfold trR
  rw [he, Matrix.trace_mul_cycle, Matrix.inv_mul_of_invertible, one_mul]

#print axioms c11_identityShift_posDef
#assert_trust kernel c11_identityShift_posDef
#print axioms c11_inv_eq_cfc
#assert_trust kernel c11_inv_eq_cfc
#print axioms c11_trR_log_eq_log_det
#assert_trust kernel c11_trR_log_eq_log_det
#print axioms c11_trR_log_normalized_congruence
#assert_trust kernel c11_trR_log_normalized_congruence
#print axioms c11_trR_congruence_mul_inv
#assert_trust kernel c11_trR_congruence_mul_inv

end NLA.MI27
