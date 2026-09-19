/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi27_route_referee1.

Original question: Audenaert and Kittaneh. Analytic resolution: Sidney Holden,
Flatiron Institute, Simons Foundation. The CFC naturality proof follows George
Stepaniants's accepted MI24 PolarPowers source pattern, developed with Codex
agent /root/nm04_final_referee1, generalized here to arbitrary scalar functions
on a finite Hermitian spectrum. That additional MI24 module is not imported;
the seven-module retained MI24 dependency closure and its credits are unchanged.
-/
import NLA.MI27.Definitions
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Algebra.Star.UnitaryStarAlgAut

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

lemma trace_unitary_conjugate {n : ℕ} (U : unitary (Mat n)) (X : Mat n) :
    Matrix.trace ((U : Mat n) * X * (U : Mat n)ᴴ) = Matrix.trace X := by
  have hcancel : (U : Mat n)ᴴ * (U : Mat n) = 1 := Unitary.coe_star_mul_self U
  rw [Matrix.trace_mul_cycle, hcancel, one_mul]

/-- Naturality for the literal finite Hermitian CFC, including discontinuous
scalar functions whose restriction to the finite spectrum is continuous. -/
lemma cfc_unitary_conjugate {n : ℕ} (U : unitary (Mat n)) (X : Mat n)
    (hX : X.IsHermitian) (f : ℝ → ℝ) :
    cfc f ((U : Mat n) * X * (U : Mat n)ᴴ) =
      (U : Mat n) * cfc f X * (U : Mat n)ᴴ := by
  let φ := Unitary.conjStarAlgAut ℂ (Mat n) U
  have hconj := Matrix.isHermitian_mul_mul_conjTranspose (U : Mat n) hX
  have hφ : Continuous φ := by
    -- Expose only the underlying multiplication map of the bundled automorphism
    -- so the two standard continuity-of-multiplication facts apply literally.
    change Continuous (fun Y : Mat n => (U : Mat n) * Y * star (U : Mat n))
    exact (continuous_const.mul continuous_id).mul continuous_const
  have hmap := StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) φ f X
    (X.finite_real_spectrum.continuousOn f) hφ hX.isSelfAdjoint hconj.isSelfAdjoint
  simpa only [φ, Unitary.conjStarAlgAut_apply, Unitary.coe_star,
    Matrix.star_eq_conjTranspose] using hmap.symm

lemma entropy_unitary_conjugate {n : ℕ} (U : unitary (Mat n)) (X : Mat n)
    (hX : X.IsHermitian) :
    entropy ((U : Mat n) * X * (U : Mat n)ᴴ) = entropy X := by
  have hcancel : (U : Mat n)ᴴ * (U : Mat n) = 1 := Unitary.coe_star_mul_self U
  have hlog : logM ((U : Mat n) * X * (U : Mat n)ᴴ) =
      (U : Mat n) * logM X * (U : Mat n)ᴴ := by
    simpa only [logM, CFC.log] using cfc_unitary_conjugate U X hX Real.log
  have hprod : ((U : Mat n) * X * (U : Mat n)ᴴ) *
      ((U : Mat n) * logM X * (U : Mat n)ᴴ) =
      (U : Mat n) * (X * logM X) * (U : Mat n)ᴴ := by
    calc
      _ = (U : Mat n) * X * ((U : Mat n)ᴴ * (U : Mat n)) *
          logM X * (U : Mat n)ᴴ := by simp only [mul_assoc]
      _ = _ := by rw [hcancel, mul_one]; simp only [mul_assoc]
  unfold entropy trR
  rw [hlog, hprod, trace_unitary_conjugate]

end NLA.MI27
