/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi27_route_referee1.

Original question: Audenaert and Kittaneh. Analytic resolution: Sidney Holden,
Flatiron Institute, Simons Foundation. This is the positive-part variational
argument used in Holden's unitary estimate, built from the actual finite matrix
functional calculus. The accepted MI24 trace-order proofs are credited and
retained unchanged through PositiveTrace. Zero spectral values are excluded
from the maximizing projection, while repeated spectral values are retained.
-/
import NLA.MI27.PositiveTrace

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

lemma posM_posSemidef {n : ℕ} (M : Mat n) : (posM M).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact cfc_nonneg (f := fun x : ℝ => max x 0) (a := M) fun x _ => le_max_right x 0

lemma tracePos_nonneg {n : ℕ} (M : Mat n) : 0 ≤ tracePos M :=
  trR_nonneg (posM M) (posM_posSemidef M)

lemma le_posM {n : ℕ} (M : Mat n) (hM : M.IsHermitian) : M ≤ posM M := by
  have hle : cfc (id : ℝ → ℝ) M ≤ cfc (fun x : ℝ => max x 0) M :=
    cfc_mono (fun x _ => le_max_left x 0)
      (M.finite_real_spectrum.continuousOn _) (M.finite_real_spectrum.continuousOn _)
  simpa only [cfc_id ℝ M hM.isSelfAdjoint, posM] using hle

/-- Every Loewner effect is bounded by the trace of the literal positive part. -/
lemma trR_effect_mul_le_tracePos {n : ℕ} (M : Mat n) (hM : M.IsHermitian)
    (Q : Mat n) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) : trR (Q * M) ≤ tracePos M := by
  have hfirst := trR_mul_order M (posM M) Q (le_posM M hM)
    (Matrix.nonneg_iff_posSemidef.mp hQ0)
  rw [trR_mul_comm M Q, trR_mul_comm (posM M) Q] at hfirst
  have hsecond := trR_mul_order Q 1 (posM M) hQ1 (posM_posSemidef M)
  rw [one_mul] at hsecond
  simpa only [tracePos] using hfirst.trans hsecond

/-- The actual positive spectral projection, including the zero-eigenvalue convention. -/
lemma positive_spectral_projection {n : ℕ} (M : Mat n) (hM : M.IsHermitian) :
    ∃ P : Mat n, P.IsHermitian ∧ P * P = P ∧ 0 ≤ P ∧ P ≤ 1 ∧
      P * M = M * P ∧ P * M = posM M := by
  let f : ℝ → ℝ := fun x => if 0 < x then 1 else 0
  have hf : ContinuousOn f (spectrum ℝ M) := M.finite_real_spectrum.continuousOn f
  have hP0 : 0 ≤ cfc f M := cfc_nonneg fun x _ => by
    dsimp only [f]
    split_ifs <;> simp
  have hP1 : cfc f M ≤ 1 := cfc_le_one f M fun x _ => by
    dsimp only [f]
    split_ifs <;> simp
  have hP2 : cfc f M * cfc f M = cfc f M := by
    rw [← cfc_mul f f M hf hf]
    apply cfc_congr
    intro x _
    dsimp only [f]
    split_ifs <;> simp
  have hcomm : cfc f M * M = M * cfc f M := by
    have hc := (cfc_commute_cfc f (id : ℝ → ℝ) M).eq
    simpa only [cfc_id ℝ M hM.isSelfAdjoint] using hc
  have hprod : cfc f M * M = posM M := by
    calc
      cfc f M * M = cfc f M * cfc (id : ℝ → ℝ) M := by
        rw [cfc_id ℝ M hM.isSelfAdjoint]
      _ = cfc (fun x : ℝ => f x * x) M := by
        simpa only [id_eq] using
          (cfc_mul f (id : ℝ → ℝ) M hf (M.finite_real_spectrum.continuousOn _)).symm
      _ = posM M := by
        unfold posM
        apply cfc_congr
        intro x _
        by_cases hx : 0 < x
        · simp only [f, if_pos hx, one_mul, max_eq_left hx.le]
        · simp only [f, if_neg hx, zero_mul, max_eq_right (le_of_not_gt hx)]
  exact ⟨cfc f M, (cfc_predicate f M).isHermitian, hP2, hP0, hP1, hcomm, hprod⟩

/-- Any PSD upper bound controls the trace of the positive part. -/
lemma tracePos_le_trR_of_le {n : ℕ} (M X : Mat n) (hM : M.IsHermitian)
    (hX : X.PosSemidef) (hMX : M ≤ X) : tracePos M ≤ trR X := by
  obtain ⟨P, hP, hP2, hP0, hP1, hcomm, hprod⟩ := positive_spectral_projection M hM
  calc
    tracePos M = trR (P * M) := by
      simpa only [tracePos] using (congrArg trR hprod).symm
    _ = trR (M * P) := trR_mul_comm P M
    _ ≤ trR (X * P) := trR_mul_order M X P hMX (Matrix.nonneg_iff_posSemidef.mp hP0)
    _ = trR (P * X) := trR_mul_comm X P
    _ ≤ trR (1 * X) := trR_mul_order P 1 X hP1 hX
    _ = trR X := by rw [one_mul]

/-- C06. The optimizer is an attained CFC projection, and both hockey-stick
bounds follow from the actual PSD trace order and complex trace normalization. -/
theorem positive_part_variational {n : ℕ} (hn : 1 ≤ n) (M : Mat n)
    (hM : M.IsHermitian) :
    (∀ Q : Mat n, 0 ≤ Q → Q ≤ 1 → trR (Q * M) ≤ tracePos M) ∧
      (∃ P : Mat n, P.IsHermitian ∧ P * P = P ∧ 0 ≤ P ∧ P ≤ 1 ∧
        P * M = M * P ∧ trR (P * M) = tracePos M) ∧
      (∀ ρ σ : Mat n, StrictDensity ρ → StrictDensity σ →
        ∀ γ : ℝ, 1 ≤ γ → 0 ≤ E γ ρ σ ∧ E γ ρ σ ≤ 1) := by
  refine ⟨fun Q hQ0 hQ1 => trR_effect_mul_le_tracePos M hM Q hQ0 hQ1, ?_, ?_⟩
  · obtain ⟨P, hP, hP2, hP0, hP1, hcomm, hprod⟩ := positive_spectral_projection M hM
    refine ⟨P, hP, hP2, hP0, hP1, hcomm, ?_⟩
    simpa only [tracePos] using congrArg trR hprod
  · intro ρ σ hρ hσ γ hγ
    have hγ0 : (0 : ℂ) ≤ (γ : ℂ) := Complex.zero_le_real.mpr (le_trans zero_le_one hγ)
    have hγσ : ((γ : ℂ) • σ).PosSemidef := hσ.1.posSemidef.smul hγ0
    have hdiff : (ρ - (γ : ℂ) • σ).IsHermitian := hρ.1.isHermitian.sub hγσ.isHermitian
    refine ⟨tracePos_nonneg _, ?_⟩
    calc
      E γ ρ σ = tracePos (ρ - (γ : ℂ) • σ) := rfl
      _ ≤ trR ρ := tracePos_le_trR_of_le _ _ hdiff hρ.1.posSemidef
        (sub_le_self _ hγσ.nonneg)
      _ = 1 := by simp only [trR, hρ.2, Complex.one_re]

#print axioms positive_part_variational

end NLA.MI27
