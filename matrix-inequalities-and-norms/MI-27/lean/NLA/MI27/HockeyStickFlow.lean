/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/recover_published_coverage.

Original question: Audenaert and Kittaneh. Complete analytic resolution:
Sidney Holden, Center for Computational Biology, Flatiron Institute,
Simons Foundation. The accepted MI24 dependencies retain their original credits.

UNCOMPILED AUTHOR DRAFT. The author ran no Lean process. The root coordinator
must elaborate and review this file against the frozen C09 contract.

For each fixed Loewner effect, the ordinary scalar mean-value theorem and C05
bound its trace pairing along the density flow. The attained variational
optimizer is used only at the two endpoints. Simultaneous unitary invariance
moves a second-argument flow to the first argument at negative time. No
derivative of a spectral projection, almost-everywhere hypothesis, or
gamma-dependent preliminary bound occurs.
-/
import NLA.MI27.PositiveCommutator
import NLA.MI27.PositivePart
import NLA.MI27.UnitaryFlow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

/-- The actual real matrix trace as a continuous real linear map. -/
private def c09_trRCLM {n : ℕ} : Mat n →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin n) ℝ ℂ))

@[simp] private lemma c09_trRCLM_apply {n : ℕ} (X : Mat n) :
    c09_trRCLM X = trR X := rfl

lemma c09_trR_conjFlow {n : ℕ} (H X : Mat n) (hH : H.IsHermitian) (t : ℝ) :
    trR (conjFlow H X t) = trR X := by
  let U : unitary (Mat n) := ⟨flow H t, flow_mem_unitary H hH t⟩
  have ht : Matrix.trace (conjFlow H X t) = Matrix.trace X := by
    simpa only [conjFlow, U] using trace_unitary_conjugate U X
  exact congrArg Complex.re ht

/-- Differentiate a fixed effect, never a maximizing projection varying in time. -/
lemma c09_hasDerivAt_pairing {n : ℕ} (H X Q : Mat n)
    (hH : H.IsHermitian) (t : ℝ) :
    HasDerivAt (fun u : ℝ => trR (Q * conjFlow H X u))
      (trR (Q * (Complex.I • comm H (conjFlow H X t)))) t := by
  have hd := HasDerivAt.const_mul Q (hasDerivAt_conjFlow H X hH t)
  have ht := (c09_trRCLM (n := n)).hasFDerivAt.comp_hasDerivAt t hd
  simpa only [Function.comp_def, c09_trRCLM_apply] using ht

/-- Cyclicity identifies the scalar derivative with the negative of C05's pairing. -/
lemma c09_pairing_derivative_cycle {n : ℕ} (Q H X : Mat n) :
    trR (Q * (Complex.I • comm H X)) =
      -trR ((-Complex.I) • (H * comm X Q)) := by
  have hc : Matrix.trace (Q * comm H X) = Matrix.trace (H * comm X Q) := by
    simp only [comm, mul_sub, Matrix.trace_sub]
    congr 1
    · exact (Matrix.trace_mul_cycle' H X Q).symm
    · exact Matrix.trace_mul_cycle' Q X H
  unfold trR
  simp only [mul_smul_comm, Matrix.trace_smul]
  rw [hc]
  simp only [neg_smul, Complex.neg_re, neg_neg]

/-- C05 and trace normalization give the same derivative bound at every time. -/
lemma c09_pairing_derivative_bound {n : ℕ} (hn : 1 ≤ n) (H X Q : Mat n)
    (hH : H.IsHermitian) (hX : StrictDensity X)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (t : ℝ) :
    |trR (Q * (Complex.I • comm H (conjFlow H X t)))| ≤ opNorm H := by
  rw [c09_pairing_derivative_cycle, abs_neg]
  have hXt : (conjFlow H X t).PosSemidef :=
    hX.1.posSemidef.mul_mul_conjTranspose_same (flow H t)
  have htrace : trR (conjFlow H X t) = 1 := by
    rw [c09_trR_conjFlow H X hH t]
    simp only [trR, hX.2, Complex.one_re]
  simpa only [htrace, mul_one] using
    positive_commutator_trace_bound hn (conjFlow H X t) H Q hXt hH hQ0 hQ1

/-- Ordinary scalar mean-value theorem on the whole real line. -/
lemma c09_pairing_lipschitz {n : ℕ} (hn : 1 ≤ n) (H X Q : Mat n)
    (hH : H.IsHermitian) (hX : StrictDensity X)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (s t : ℝ) :
    |trR (Q * conjFlow H X t) - trR (Q * conjFlow H X s)| ≤
      |t - s| * opNorm H := by
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (Set.univ : Set ℝ))
    (f := fun u : ℝ => trR (Q * conjFlow H X u))
    (f' := fun u : ℝ => trR (Q * (Complex.I • comm H (conjFlow H X u))))
    (C := opNorm H)
    (fun u _ => (c09_hasDerivAt_pairing H X Q hH u).hasDerivWithinAt)
    (fun u _ => by
      simpa only [Real.norm_eq_abs] using
        c09_pairing_derivative_bound hn H X Q hH hX hQ0 hQ1 u)
    convex_univ (Set.mem_univ s) (Set.mem_univ t)
  simpa only [Real.norm_eq_abs, mul_comm] using hb

lemma c09_smul_isHermitian {n : ℕ} (Y : Mat n) (hY : Y.IsHermitian) (γ : ℝ) :
    ((γ : ℂ) • Y).IsHermitian := by
  have hγ : IsSelfAdjoint (γ : ℂ) := by
    change star (γ : ℂ) = (γ : ℂ)
    simp only [Complex.star_def, Complex.conj_ofReal]
  exact hY.smul hγ

/-- Fix an attained optimizer at the later endpoint and test it at the other one.
The parameter gamma appears only in the constant term, which cancels exactly. -/
lemma c09_first_flow_sub_le {n : ℕ} (hn : 1 ≤ n) (X Y H : Mat n)
    (hX : StrictDensity X) (hY : Y.IsHermitian) (hH : H.IsHermitian)
    (γ s t : ℝ) :
    E γ (conjFlow H X t) Y - E γ (conjFlow H X s) Y ≤ |t - s| * opNorm H := by
  have hM : ∀ u : ℝ, (conjFlow H X u - (γ : ℂ) • Y).IsHermitian := by
    intro u
    exact (Matrix.isHermitian_mul_mul_conjTranspose (flow H u) hX.1.isHermitian).sub
      (c09_smul_isHermitian Y hY γ)
  obtain ⟨Q, hQ, hQ2, hQ0, hQ1, hcomm, hvalue⟩ :=
    (positive_part_variational hn (conjFlow H X t - (γ : ℂ) • Y) (hM t)).2.1
  have htest := trR_effect_mul_le_tracePos
    (conjFlow H X s - (γ : ℂ) • Y) (hM s) Q hQ0 hQ1
  change tracePos (conjFlow H X t - (γ : ℂ) • Y) -
    tracePos (conjFlow H X s - (γ : ℂ) • Y) ≤ _
  calc
    tracePos (conjFlow H X t - (γ : ℂ) • Y) -
        tracePos (conjFlow H X s - (γ : ℂ) • Y) ≤
        trR (Q * (conjFlow H X t - (γ : ℂ) • Y)) -
          trR (Q * (conjFlow H X s - (γ : ℂ) • Y)) := by
      rw [hvalue]
      exact sub_le_sub_left htest _
    _ = trR (Q * conjFlow H X t) - trR (Q * conjFlow H X s) := by
      simp only [mul_sub, trR, Matrix.trace_sub, Complex.sub_re]
      ring
    _ ≤ |trR (Q * conjFlow H X t) - trR (Q * conjFlow H X s)| := le_abs_self _
    _ ≤ |t - s| * opNorm H := c09_pairing_lipschitz hn H X Q hH hX hQ0 hQ1 s t

/-- Reversing the endpoint optimizer proves the absolute finite-difference bound. -/
lemma c09_first_flow_lipschitz {n : ℕ} (hn : 1 ≤ n) (X Y H : Mat n)
    (hX : StrictDensity X) (hY : Y.IsHermitian) (hH : H.IsHermitian)
    (γ s t : ℝ) :
    |E γ (conjFlow H X t) Y - E γ (conjFlow H X s) Y| ≤ |t - s| * opNorm H := by
  have hu := c09_first_flow_sub_le hn X Y H hX hY hH γ s t
  have hl := c09_first_flow_sub_le hn X Y H hX hY hH γ t s
  rw [abs_sub_comm s t] at hl
  refine abs_le.mpr ⟨?_, hu⟩
  simpa only [neg_sub] using neg_le_neg hl

/-- Simultaneous conjugation preserves the actual CFC hockey-stick expression. -/
lemma c09_E_unitary_conjugate {n : ℕ} (U : unitary (Mat n)) (X Y : Mat n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (γ : ℝ) :
    E γ ((U : Mat n) * X * (U : Mat n)ᴴ)
      ((U : Mat n) * Y * (U : Mat n)ᴴ) = E γ X Y := by
  have hM := hX.sub (c09_smul_isHermitian Y hY γ)
  have hd : (U : Mat n) * X * (U : Mat n)ᴴ -
      (γ : ℂ) • ((U : Mat n) * Y * (U : Mat n)ᴴ) =
      (U : Mat n) * (X - (γ : ℂ) • Y) * (U : Mat n)ᴴ := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
  unfold E tracePos posM trR
  rw [hd, cfc_unitary_conjugate U (X - (γ : ℂ) • Y) hM,
    trace_unitary_conjugate]

/-- The group law alone cancels the two conjugations at opposite times. -/
lemma c09_conjFlow_neg_cancel {n : ℕ} (H X : Mat n) (t : ℝ) :
    conjFlow H (conjFlow H X t) (-t) = X := by
  have hc : flow H (-t) * flow H t = 1 := by
    rw [← flow_add, neg_add_cancel, flow_zero]
  calc
    conjFlow H (conjFlow H X t) (-t) =
        (flow H (-t) * flow H t) * X * (flow H (-t) * flow H t)ᴴ := by
      simp only [conjFlow, Matrix.conjTranspose_mul, mul_assoc]
    _ = X := by rw [hc, Matrix.conjTranspose_one, one_mul, mul_one]

/-- Move a second-argument flow onto the normalized first argument at negative time. -/
lemma c09_move_flow {n : ℕ} (X Y H : Mat n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (hH : H.IsHermitian) (γ t : ℝ) :
    E γ X (conjFlow H Y t) = E γ (conjFlow H X (-t)) Y := by
  let U : unitary (Mat n) := ⟨flow H (-t), flow_mem_unitary H hH (-t)⟩
  have hYt : (conjFlow H Y t).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose (flow H t) hY
  have hu := c09_E_unitary_conjugate U X (conjFlow H Y t) hX hYt γ
  change E γ (conjFlow H X (-t)) (conjFlow H (conjFlow H Y t) (-t)) =
    E γ X (conjFlow H Y t) at hu
  rw [c09_conjFlow_neg_cancel H Y t] at hu
  exact hu.symm

/-- C09. The exact frozen contract: both arguments, all real times, no dimension
or gamma factor. The helpers actually establish the same estimate for every
real gamma; the original gamma≥1 hypothesis is retained in this export. -/
theorem hockey_stick_unitary_lipschitz {n : ℕ} (hn : 1 ≤ n) (ρ σ H : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ) (hH : H.IsHermitian)
    (γ s t : ℝ) (hγ : 1 ≤ γ) :
    |E γ ρ (conjFlow H σ t) - E γ ρ (conjFlow H σ s)| ≤ |t - s| * opNorm H ∧
      |E γ (conjFlow H σ t) ρ - E γ (conjFlow H σ s) ρ| ≤
        |t - s| * opNorm H := by
  constructor
  · rw [c09_move_flow ρ σ H hρ.1.isHermitian hσ.1.isHermitian hH γ t,
      c09_move_flow ρ σ H hρ.1.isHermitian hσ.1.isHermitian hH γ s]
    have hb := c09_first_flow_lipschitz hn ρ σ H hρ hσ.1.isHermitian hH γ (-s) (-t)
    have htime : |(-t) - (-s)| = |t - s| := by rw [neg_sub_neg, abs_sub_comm]
    simpa only [htime] using hb
  · exact c09_first_flow_lipschitz hn σ ρ H hσ hρ.1.isHermitian hH γ s t

#print axioms hockey_stick_unitary_lipschitz
#assert_trust kernel hockey_stick_unitary_lipschitz

end NLA.MI27
