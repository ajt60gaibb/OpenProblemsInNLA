/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.
-/
import NLA.MF24.SpectralBridge
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF24
open scoped BigOperators

lemma spectralNorm_conjTranspose {N : ℕ} (A : Square N) :
    spectralNorm A.conjTranspose = spectralNorm A := by
  open scoped Matrix.Norms.L2Operator in
    simpa only [spectralNorm, Matrix.l2_opNorm_toEuclideanCLM] using
      Matrix.l2_opNorm_conjTranspose A

lemma row_energy_le_spectralNorm_sq {N : ℕ} (A : Square N) (r : Fin N) :
    ∑ s : Fin N, ‖A r s‖ ^ 2 ≤ spectralNorm A ^ 2 := by
  let e : EuclideanVector N := PiLp.single 2 r (1 : ℂ)
  let T := Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) A.conjTranspose
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  have hbound : ‖T e‖ ≤ spectralNorm A := by
    calc ‖T e‖ ≤ ‖T‖ * ‖e‖ := T.le_opNorm e
      _ = spectralNorm A := by
        rw [he, mul_one]
        exact spectralNorm_conjTranspose A
  have hentry : ∀ s : Fin N, (T e) s = star (A r s) := by
    intro s
    change (Matrix.mulVec A.conjTranspose (Pi.single r (1 : ℂ))) s = star (A r s)
    simp [Matrix.mulVec_single_one, Matrix.conjTranspose_apply]
  have henergy : ‖T e‖ ^ 2 = ∑ s : Fin N, ‖A r s‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro s _
    rw [hentry]
    simp
  rw [← henergy]
  exact (sq_le_sq₀ (norm_nonneg _) (spectralNorm_nonneg A)).mpr hbound

lemma spectralNorm_le_of_energy {N : ℕ} (A : Square N) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x : EuclideanVector N,
      ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) A x‖ ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2) :
    spectralNorm A ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mp
  simpa only [mul_pow] using h x

#assert_trust kernel row_energy_le_spectralNorm_sq

end NLA.MF24
