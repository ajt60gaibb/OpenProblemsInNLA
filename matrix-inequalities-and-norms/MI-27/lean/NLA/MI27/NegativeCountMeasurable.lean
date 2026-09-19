/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nr04_mf14_final_referee_a.

Original MI27 question: Audenaert and Kittaneh. Analytic resolution: Sidney
Holden, Flatiron Institute, Simons Foundation. The identity-shift route is
based on Peter E. Frenkel. This module proves measurability of the strict
negative spectral count along the two-variable Hermitian pencil by actual
continuous positive-part trace approximations. No eigenbasis selection or
simple-eigenvalue premise is used. Retained spectral/trace credits remain
in imported files. This is partial C11 development, not the full identity.
Exact headers approved before bodies in NEGATIVE-COUNT-LAYERCAKE-STATEMENTS.md.
-/
import NLA.MI27.NegativeCount
import NLA.MI27.PositivePartLipschitz
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator Topology
open Filter Set
noncomputable section
namespace NLA.MI27

/-- Positive-part trace difference quotients with positive reciprocal step. -/
def c11_negativeCountApprox {n : ℕ} (M : Mat n) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) *
    (tracePos (-M) -
      tracePos (-(c11_identityShift M (1 / ((k : ℝ) + 1)))))

lemma c11_scalar_negativeCountApprox_eventually (x : ℝ) :
    ∀ᶠ k : ℕ in Filter.atTop,
      ((k : ℝ) + 1) * (max (-x) 0 - max (-(x + 1 / ((k : ℝ) + 1))) 0) =
        if x < 0 then (1 : ℝ) else 0 := by
  by_cases hx : x < 0
  · have hstep : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < -x :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (Iio_mem_nhds (neg_pos.mpr hx))
    filter_upwards [hstep] with k hk
    have hkpos : 0 < (k : ℝ) + 1 := by positivity
    rw [if_pos hx, max_eq_left (neg_nonneg.mpr hx.le),
      max_eq_left (show 0 ≤ -(x + 1 / ((k : ℝ) + 1)) by linarith)]
    field_simp [hkpos.ne']
    <;> ring
  · apply Eventually.of_forall
    intro k
    have hx0 : 0 ≤ x := le_of_not_gt hx
    have hstep : 0 ≤ 1 / ((k : ℝ) + 1) := by positivity
    rw [if_neg hx, max_eq_right (neg_nonpos.mpr hx0),
      max_eq_right (neg_nonpos.mpr (add_nonneg hx0 hstep))]
    ring

/-- A fixed finite spectrum has only finitely many strictly negative gaps from zero. -/
lemma c11_negativeCountApprox_eventually {n : ℕ} (hn : 1 ≤ n) (M : Mat n)
    (hM : M.IsHermitian) :
    ∀ᶠ k : ℕ in Filter.atTop, c11_negativeCountApprox M k = c11_negativeCount M := by
  have he : ∀ᶠ k : ℕ in atTop, ∀ i : Fin n,
      ((k : ℝ) + 1) *
        (max (-hM.eigenvalues i) 0 -
          max (-(hM.eigenvalues i + 1 / ((k : ℝ) + 1))) 0) =
        if hM.eigenvalues i < 0 then (1 : ℝ) else 0 :=
    Filter.eventually_all.mpr (fun i => c11_scalar_negativeCountApprox_eventually _)
  filter_upwards [he] with k hk
  have hzero : tracePos (-M) = ∑ i : Fin n, max (-hM.eigenvalues i) 0 := by
    simpa only [c11_identityShift, Complex.ofReal_zero, zero_smul, add_zero] using
      c11_tracePos_neg_identityShift hn M hM 0
  unfold c11_negativeCountApprox
  rw [hzero, c11_tracePos_neg_identityShift hn M hM, c11_negativeCount_spectral hn M hM,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => hk i)

/-- C07 supplies continuity along any continuous Hermitian family. -/
lemma c11_tracePos_continuous_comp {n : ℕ} (hn : 1 ≤ n)
    {α : Type*} [TopologicalSpace α] (F : α → Mat n)
    (hF : Continuous F) (hFH : ∀ x, (F x).IsHermitian) :
    Continuous (fun x => tracePos (F x)) := by
  have hc : Continuous (fun M : {M : Mat n // M.IsHermitian} => tracePos M.1) := by
    apply (LipschitzWith.of_dist_le' (K := (n : ℝ)) ?_).continuous
    intro M N
    simpa only [Real.dist_eq, Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs, opNorm_eq_l2] using
      positive_part_trace_lipschitz hn M.1 N.1 M.2 N.2
  exact hc.comp (hF.subtype_mk hFH)

/-- Joint measurability includes all singular pencil parameters and repeated eigenvalues. -/
lemma c11_negativeCount_pencil_measurable {n : ℕ} (hn : 1 ≤ n) (X Y : Mat n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    Measurable (fun z : ℝ × ℝ =>
      c11_negativeCount
        (c11_identityShift (X + (z.1 : ℂ) • (Y - X)) z.2)) := by
  let F : ℝ × ℝ → Mat n := fun z =>
    c11_identityShift (X + (z.1 : ℂ) • (Y - X)) z.2
  have hF : Continuous F := by
    dsimp [F, c11_identityShift]
    fun_prop
  have hFH (z : ℝ × ℝ) : (F z).IsHermitian :=
    (hX.add ((hY.sub hX).smul (by simp [IsSelfAdjoint]))).add
      (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint]))
  have happ (k : ℕ) : Continuous (fun z => c11_negativeCountApprox (F z) k) := by
    have hc₀ : Continuous (fun z => tracePos (-(F z))) :=
      c11_tracePos_continuous_comp hn _ hF.neg (fun z => (hFH z).neg)
    have hc₁ : Continuous (fun z =>
        tracePos (-(c11_identityShift (F z) (1 / ((k : ℝ) + 1))))) := by
      apply c11_tracePos_continuous_comp hn
      · unfold c11_identityShift
        fun_prop
      · intro z
        exact ((hFH z).add
          (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint]))).neg
    exact (hc₀.sub hc₁).const_mul ((k : ℝ) + 1)
  change Measurable (fun z => c11_negativeCount (F z))
  apply measurable_of_tendsto_metrizable (fun k => (happ k).measurable)
  apply tendsto_pi_nhds.mpr
  intro z
  exact (Filter.tendsto_congr' (c11_negativeCountApprox_eventually hn (F z) (hFH z))).2
    tendsto_const_nhds

#print axioms c11_scalar_negativeCountApprox_eventually
#print axioms c11_negativeCountApprox_eventually
#print axioms c11_tracePos_continuous_comp
#print axioms c11_negativeCount_pencil_measurable

end NLA.MI27
