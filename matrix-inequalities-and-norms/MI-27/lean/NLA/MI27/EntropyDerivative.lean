/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/recover_published_coverage.

Original MI27 resolution: Sidney Holden, Center for Computational Biology,
Flatiron Institute, Simons Foundation. Existing MI24/MI27 sources retain
their original mathematical and code credits.

UNCOMPILED full C16 source draft, requiring root compilation and independent
review. The trace tangent sandwich is proved internally in TraceTangent.
The actual matrix logarithm is used only through its proved continuity on
selfadjoint units. No noncommutative matrix-log derivative is assumed.
-/
import NLA.MI27.TraceTangent
import NLA.MI27.HockeyStickFlow
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Operator.Asymptotics
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator Topology
open Filter Asymptotics
noncomputable section
namespace NLA.MI27

/-- The same concrete continuous real trace map as in C09; no norm estimate is postulated. -/
private def c16_trRCLM {n : ℕ} : Mat n →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin n) ℝ ℂ))

@[simp] private lemma c16_trRCLM_apply {n : ℕ} (X : Mat n) :
    c16_trRCLM X = trR X := rfl

private lemma c16_trR_zero {n : ℕ} : trR (0 : Mat n) = 0 := by
  simp only [trR, Matrix.trace_zero, Complex.zero_re]

/-- Pinned CFC continuity applies along every actual positive-definite path. -/
lemma c16_log_continuous_of_posDef {n : ℕ} (F : ℝ → Mat n)
    (hF : Continuous F) (hPD : ∀ u : ℝ, (F u).PosDef) :
    Continuous (fun u : ℝ => logM (F u)) := by
  let : NormedAlgebra ℝ (Mat n) := .restrictScalars ℝ ℂ (Mat n)
  have hc := (CFC.continuousOn_log (A := Mat n)).comp_continuous hF
    (fun u => ⟨(hPD u).isHermitian.isSelfAdjoint, (hPD u).isUnit⟩)
  simpa only [Function.comp_def, logM] using hc

/-- Trace differentiation from the internally proved two-sided tangent inequality.
Every matrix in the path is positive definite, but spectra may have repetitions.
The path's derivative need not commute with the matrix at the base point. -/
lemma c16_hasDerivAt_entropy_of_posDef {n : ℕ} (hn : 1 ≤ n) (F : ℝ → Mat n)
    (hF : Continuous F) (hPD : ∀ u : ℝ, (F u).PosDef) (F' : Mat n) (t : ℝ)
    (hd : HasDerivAt F F' t) :
    HasDerivAt (fun u : ℝ => entropy (F u))
      (-trR ((logM (F t) + 1) * F')) t := by
  let G : Mat n := logM (F t) + 1
  let R : ℝ → ℝ := fun u =>
    entropy (F u) - entropy (F t) + trR (G * (F u - F t))
  let P : ℝ → Mat n := fun u =>
    (logM (F u) - logM (F t)) * (F u - F t)
  have hlog : (fun u : ℝ => logM (F u) - logM (F t)) =o[𝓝 t]
      (fun _ : ℝ => (1 : ℝ)) := by
    apply (isLittleO_one_iff ℝ).2
    have hc : Tendsto (fun u : ℝ => logM (F u)) (𝓝 t) (𝓝 (logM (F t))) :=
      (c16_log_continuous_of_posDef F hF hPD).continuousAt.tendsto
    have hk : Tendsto (fun _ : ℝ => logM (F t)) (𝓝 t) (𝓝 (logM (F t))) :=
      tendsto_const_nhds
    simpa only [sub_self] using hc.sub hk
  have hinc : (fun u : ℝ => F u - F t) =O[𝓝 t] (fun u : ℝ => u - t) :=
    hd.isBigO_sub
  have hp : P =o[𝓝 t] (fun u : ℝ => u - t) := by
    simpa only [P, one_mul] using hlog.mul_isBigO hinc
  have htrace : (fun u : ℝ => trR (P u)) =o[𝓝 t] (fun u : ℝ => u - t) := by
    have hc := ((c16_trRCLM (n := n)).isBigO_comp P (𝓝 t)).trans_isLittleO hp
    simpa only [Function.comp_def, c16_trRCLM_apply] using hc
  have hnorm : ∀ u : ℝ, ‖R u‖ ≤ ‖trR (P u)‖ := by
    intro u
    obtain ⟨hl, hu⟩ := c16_entropy_tangent_sandwich hn (F t) (F u) (hPD t) (hPD u)
    have hdiff :
        trR ((logM (F u) + 1) * (F u - F t)) - trR (G * (F u - F t)) =
          trR (P u) := by
      simp only [G, P, add_mul, sub_mul, trR, Matrix.trace_add, Matrix.trace_sub,
        Complex.add_re, Complex.sub_re]
      ring
    have hR0 : R u ≤ 0 := by
      dsimp only [R, G]
      linarith
    have hRP : -R u ≤ trR (P u) := by
      dsimp only [R]
      linarith [hl, hdiff]
    calc
      ‖R u‖ = -R u := by rw [Real.norm_eq_abs, abs_of_nonpos hR0]
      _ ≤ trR (P u) := hRP
      _ ≤ ‖trR (P u)‖ := by simpa only [Real.norm_eq_abs] using le_abs_self (trR (P u))
  have hr : R =o[𝓝 t] (fun u : ℝ => u - t) :=
    (isBigO_of_le (𝓝 t) hnorm).trans_isLittleO htrace
  have hlin : HasDerivAt (fun u : ℝ => -trR (G * (F u - F t)))
      (-trR (G * F')) t := by
    have hm := HasDerivAt.const_mul G (hd.sub_const (F t))
    have ht : HasDerivAt (fun u : ℝ => trR (G * (F u - F t)))
        (trR (G * F')) t := by
      have hc := (c16_trRCLM (n := n)).hasFDerivAt.comp_hasDerivAt t hm
      simpa only [Function.comp_def, c16_trRCLM_apply] using hc
    exact ht.neg
  have hl : (fun u : ℝ => -trR (G * (F u - F t)) -
      (u - t) * (-trR (G * F'))) =o[𝓝 t] (fun u : ℝ => u - t) := by
    simpa only [sub_self, mul_zero, c16_trR_zero, neg_zero, sub_zero, smul_eq_mul] using
      hlin.isLittleO
  have hsum : (fun u : ℝ => R u + (-trR (G * (F u - F t)) -
      (u - t) * (-trR (G * F')))) =o[𝓝 t] (fun u : ℝ => u - t) := hr.add hl
  have hrem : (fun u : ℝ => entropy (F u) - entropy (F t) -
      (u - t) • (-trR ((logM (F t) + 1) * F'))) =o[𝓝 t]
      (fun u : ℝ => u - t) := by
    apply hsum.congr_left
    intro u
    dsimp only [R, G]
    simp only [smul_eq_mul]
    ring
  exact HasDerivAt.of_isLittleO hrem

lemma c16_trR_I_comm_zero {n : ℕ} (H B : Mat n) :
    trR (Complex.I • comm H B) = 0 := by
  simp only [trR, Matrix.trace_smul, comm, Matrix.trace_sub]
  rw [Matrix.trace_mul_comm H B]
  simp only [sub_self, smul_zero, Complex.zero_re]

/-- The exact coefficient and sign in the frozen C16 statement. -/
lemma c16_entropy_derivative_coefficient {n : ℕ} (H B L : Mat n) :
    -trR ((L + 1) * (Complex.I • comm H B)) =
      trR (H * ((-Complex.I) • comm B L)) := by
  have hsplit : trR ((L + 1) * (Complex.I • comm H B)) =
      trR (L * (Complex.I • comm H B)) + trR (Complex.I • comm H B) := by
    simp only [add_mul, one_mul, trR, Matrix.trace_add, Complex.add_re]
  rw [hsplit, c16_trR_I_comm_zero, add_zero, c09_pairing_derivative_cycle,
    neg_neg, mul_smul_comm]

/-- C16. Exact frozen statement, derived internally from trace tangency,
log continuity, and the actual noncommutative flow derivative. -/
theorem entropy_unitary_mix_derivative {n : ℕ} (hn : 1 ≤ n) (A B H : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (hH : H.IsHermitian) :
    HasDerivAt (fun t : ℝ => entropy (A + conjFlow H B t))
      (trR (H * ((-Complex.I) • comm B (logM (A + B))))) 0 := by
  let T : ℝ → Mat n := fun t => A + conjFlow H B t
  have hT : Continuous T := by
    apply continuous_const.add
    exact continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_conjFlow H B hH t).continuousAt
  have hPD : ∀ t : ℝ, (T t).PosDef := by
    intro t
    have hBt : (conjFlow H B t).PosDef :=
      ((unitary_flow_semantics hn H hH).2.2.2 B t).2.2.1 hB
    exact hA.add hBt
  have hd : HasDerivAt T (Complex.I • comm H B) 0 := by
    simpa only [T, conjFlow, flow_zero, Matrix.conjTranspose_one, one_mul, mul_one] using
      (hasDerivAt_conjFlow H B hH 0).const_add A
  have he := c16_hasDerivAt_entropy_of_posDef hn T hT hPD (Complex.I • comm H B) 0 hd
  have hT0 : T 0 = A + B := by
    simp only [T, conjFlow, flow_zero, Matrix.conjTranspose_one, one_mul, mul_one]
  rw [hT0, c16_entropy_derivative_coefficient H B (logM (A + B))] at he
  exact he

#print axioms entropy_unitary_mix_derivative
#assert_trust kernel entropy_unitary_mix_derivative

end NLA.MI27
