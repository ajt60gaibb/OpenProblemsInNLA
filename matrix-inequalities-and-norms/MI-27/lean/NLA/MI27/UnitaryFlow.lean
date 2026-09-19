/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi27_route_referee1;
local compilation repairs by Codex /root.

Original question: Audenaert and Kittaneh. Analytic resolution: Sidney Holden,
Flatiron Institute, Simons Foundation. This module uses Mathlib's derivative
theorem for real scalar multiples of a fixed element in a possibly
noncommutative Banach algebra, followed by the real star and product rules.
It does not assume the invalid general noncommuting scalar exponential rule.
-/
import NLA.MI27.UnitaryConjugation
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

/-- Explicit scalar-tower bridge from the frozen complex formula to real time. -/
lemma flow_eq_exp_real_smul {n : ℕ} (H : Mat n) (t : ℝ) :
    flow H t = NormedSpace.exp (t • (Complex.I • H)) := by
  unfold flow
  congr 1
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, mul_comm]
  rfl

lemma flow_zero {n : ℕ} (H : Mat n) : flow H 0 = 1 := by
  simp only [flow, Complex.ofReal_zero, mul_zero, zero_smul, NormedSpace.exp_zero]

lemma flow_add {n : ℕ} (H : Mat n) (s t : ℝ) :
    flow H (s + t) = flow H s * flow H t := by
  let : NormedAlgebra ℚ (Mat n) := .restrictScalars ℚ ℂ (Mat n)
  simp only [flow_eq_exp_real_smul, add_smul]
  exact NormedSpace.exp_add_of_commute
    (((Commute.refl (Complex.I • H)).smul_left s).smul_right t)

lemma flow_mem_unitary {n : ℕ} (H : Mat n) (hH : H.IsHermitian) (t : ℝ) :
    flow H t ∈ unitary (Mat n) := by
  let : NormedAlgebra ℚ (Mat n) := .restrictScalars ℚ ℂ (Mat n)
  have hs : Complex.I * (t : ℂ) ∈ skewAdjoint ℂ := by
    rw [skewAdjoint.mem_iff]
    simp only [Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  simpa only [flow] using NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    (hH.isSelfAdjoint.smul_mem_skewAdjoint hs)

lemma flow_unitary {n : ℕ} (H : Mat n) (hH : H.IsHermitian) (t : ℝ) :
    (flow H t)ᴴ * flow H t = 1 ∧ flow H t * (flow H t)ᴴ = 1 := by
  simpa only [Matrix.star_eq_conjTranspose] using
    (Unitary.mem_iff.mp (flow_mem_unitary H hH t))

lemma hasDerivAt_flow {n : ℕ} (H : Mat n) (t : ℝ) :
    HasDerivAt (flow H) (Complex.I • (H * flow H t)) t := by
  let : NormedAlgebra ℝ (Mat n) := .restrictScalars ℝ ℂ (Mat n)
  have heq : flow H = fun s : ℝ => NormedSpace.exp (s • (Complex.I • H)) :=
    funext (flow_eq_exp_real_smul H)
  simpa only [heq, smul_mul_assoc] using
    hasDerivAt_exp_smul_const' (Complex.I • H) t

lemma hasDerivAt_conjFlow {n : ℕ} (H σ : Mat n) (hH : H.IsHermitian) (t : ℝ) :
    HasDerivAt (conjFlow H σ) (Complex.I • comm H (conjFlow H σ t)) t := by
  have hd := ((hasDerivAt_flow H t).mul_const σ).mul (hasDerivAt_flow H t).star
  have hd' : HasDerivAt (fun s : ℝ => conjFlow H σ s)
      (((Complex.I • (H * flow H t)) * σ) * (flow H t)ᴴ +
        (flow H t * σ) * ((-Complex.I) • ((flow H t)ᴴ * H))) t := by
    -- The real star derivative reverses the matrix factors and conjugates i.
    -- Normalize that star to the frozen conjugate-transpose notation explicitly.
    convert hd using 1 <;> try rfl
    change ((Complex.I • (H * flow H t)) * σ) * (flow H t)ᴴ +
        (flow H t * σ) * ((-Complex.I) • ((flow H t)ᴴ * H)) =
      ((Complex.I • (H * flow H t)) * σ) * (flow H t)ᴴ +
        (flow H t * σ) * (Complex.I • (H * flow H t))ᴴ
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Complex.star_def, Complex.conj_I, hH.eq]
  apply hd'.congr_deriv
  simp only [conjFlow, comm, smul_mul_assoc, mul_smul_comm, neg_smul, mul_neg,
    sub_eq_add_neg, smul_add, smul_neg, mul_assoc]

/-- C08. Every time and every conjugated matrix is retained; all derivatives
are real derivatives of the frozen exponential and multiplication formulas. -/
theorem unitary_flow_semantics {n : ℕ} (hn : 1 ≤ n) (H : Mat n)
    (hH : H.IsHermitian) :
    flow H 0 = 1 ∧
      (∀ s t : ℝ, flow H (s + t) = flow H s * flow H t) ∧
      (∀ t : ℝ, (flow H t)ᴴ * flow H t = 1 ∧ flow H t * (flow H t)ᴴ = 1 ∧
        HasDerivAt (flow H) (Complex.I • (H * flow H t)) t) ∧
      (∀ (σ : Mat n) (t : ℝ),
        (σ.IsHermitian → (conjFlow H σ t).IsHermitian) ∧
        (σ.PosSemidef → (conjFlow H σ t).PosSemidef) ∧
        (σ.PosDef → (conjFlow H σ t).PosDef) ∧
        Matrix.trace (conjFlow H σ t) = Matrix.trace σ ∧
        spectrum ℂ (conjFlow H σ t) = spectrum ℂ σ ∧
        (σ.IsHermitian → entropy (conjFlow H σ t) = entropy σ) ∧
        HasDerivAt (conjFlow H σ)
          (Complex.I • comm H (conjFlow H σ t)) t) := by
  refine ⟨flow_zero H, flow_add H, ?_, ?_⟩
  · intro t
    have hu := flow_unitary H hH t
    exact ⟨hu.1, hu.2, hasDerivAt_flow H t⟩
  · intro σ t
    let U : unitary (Mat n) := ⟨flow H t, flow_mem_unitary H hH t⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hasDerivAt_conjFlow H σ hH t⟩
    · intro hσ
      exact Matrix.isHermitian_mul_mul_conjTranspose (flow H t) hσ
    · intro hσ
      exact hσ.mul_mul_conjTranspose_same (flow H t)
    · intro hσ
      have hp := (Matrix.IsUnit.posDef_star_right_conjugate_iff
        (x := σ) (Unitary.isUnit_coe (U := U))).mpr hσ
      simpa only [conjFlow, U, Matrix.star_eq_conjTranspose] using hp
    · simpa only [conjFlow, U] using trace_unitary_conjugate U σ
    · simpa only [conjFlow, U, Unitary.coe_star, Matrix.star_eq_conjTranspose] using
        (Unitary.spectrum_star_right_conjugate (R := ℂ) (U := U) (a := σ))
    · intro hσ
      simpa only [conjFlow, U] using entropy_unitary_conjugate U σ hσ

#print axioms unitary_flow_semantics

end NLA.MI27
