import ProofProject.ReplicationBound
import ProofProject.CoefficientSquare

/-!
# Endpoint deficits from the boundary coefficient estimate

The endpoint estimates apply to every coefficient. At the quadratic minimizers,
they control both inner products needed by the replication construction.
-/

noncomputable section

namespace ProofProject

/-- The retained-endpoint minimizer controls both original inner products with
an absolute factor four. The relation is the stationary equation. -/
lemma minimizer_inner_energy_le {m : ℝ} (hm : 1 ≤ m) (b₀ b₁ t : ℂ)
    (hrel : (m : ℂ) * (b₀ + t) = b₁ + t) :
    ‖b₀‖ ^ 2 + ‖b₁‖ ^ 2 ≤ 4 * (‖t‖ ^ 2 + ‖b₁ + t‖ ^ 2) := by
  have hm0 : 0 ≤ m := by linarith
  have hn : m * ‖b₀ + t‖ = ‖b₁ + t‖ := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm0]
      using congrArg norm hrel
  have hcompare : ‖b₀ + t‖ ≤ ‖b₁ + t‖ := by
    calc
      _ ≤ m * ‖b₀ + t‖ := le_mul_of_one_le_left (norm_nonneg _) hm
      _ = _ := hn
  have h₀ : ‖b₀‖ ≤ ‖b₁ + t‖ + ‖t‖ := by
    have h := norm_sub_le (b₀ + t) t
    simp only [add_sub_cancel_right] at h
    exact h.trans (add_le_add hcompare le_rfl)
  have h₁ : ‖b₁‖ ≤ ‖b₁ + t‖ + ‖t‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (b₁ + t) t
  have h₀sq := pow_le_pow_left₀ (norm_nonneg _) h₀ 2
  have h₁sq := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
  nlinarith [sq_nonneg (‖b₁ + t‖ - ‖t‖)]

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

/-- The source's boundary estimate, expressed at the two endpoints of a single
coefficient of the weighted family. -/
def HasBoundaryEstimate (f : Fin n → H) (M B : ℝ) : Prop :=
  ∀ (a : Fin n → ℂ) (i : Fin n) (t : ℂ),
    (‖t‖ ^ 2 + ‖inner ℂ (f i) (replicationTail f a i)‖ ^ 2 ≤
      B * coefficientDeficit M (replicationBase f a i) (replicationTail f a i) (f i) t 0) ∧
    (‖t‖ ^ 2 + ‖inner ℂ (f i) (replicationTail f a i + t • f i)‖ ^ 2 ≤
      B * coefficientDeficit M (replicationBase f a i) (replicationTail f a i) (f i) t 1)

/-- The zero-coefficient endpoint gives the tail bound needed for the
interior completed-square estimate. -/
lemma boundary_zero_tail_bound {M B : ℝ} (hM : 0 ≤ M) (hB : 0 < B)
    (v y e : H)
    (hzero : ∀ t : ℂ, ‖t‖ ^ 2 + ‖inner ℂ e y‖ ^ 2 ≤
      B * coefficientDeficit M v y e t 0) :
    ‖y‖ ≤ M * ‖v‖ := by
  have hb := hzero 0
  simp only [coefficientDeficit, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_mul, zero_smul, add_zero, zero_add] at hb
  have hp : 0 ≤ B * (M ^ 2 * ‖v‖ ^ 2 - ‖y‖ ^ 2) := (sq_nonneg _).trans hb
  have hδ : 0 ≤ M ^ 2 * ‖v‖ ^ 2 - ‖y‖ ^ 2 :=
    (mul_nonneg_iff_of_pos_left hB).mp hp
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp
  rw [mul_pow]
  linarith

/-- The deleted-endpoint boundary estimate controls the two correlations at
the exact minimizing coefficient, hence at every coefficient. -/
lemma coefficientDeficit_zero_lower {M B : ℝ} (hM : 1 < M) (hB : 0 < B)
    (v y e : H) (he : ‖e‖ = 1)
    (hzero : ∀ t : ℂ, ‖t‖ ^ 2 + ‖inner ℂ e y‖ ^ 2 ≤
      B * coefficientDeficit M v y e t 0) (t : ℂ) :
    (1 / (4 * B)) * (‖inner ℂ e v‖ ^ 2 + ‖inner ℂ e y‖ ^ 2) ≤
      coefficientDeficit M v y e t 0 := by
  have hb := hzero (-inner ℂ e v)
  simp only [norm_neg] at hb
  have hm := coefficientDeficit_minimum_le hM v y e he t (z := 0) (by simp)
  rw [coefficientMinimizer_zero hM] at hm
  have htotal := hb.trans (mul_le_mul_of_nonneg_left hm hB.le)
  have hδ : 0 ≤ coefficientDeficit M v y e t 0 := by
    exact (mul_nonneg_iff_of_pos_left hB).mp ((by positivity :
      0 ≤ ‖inner ℂ e v‖ ^ 2 + ‖inner ℂ e y‖ ^ 2).trans htotal)
  have h : (‖inner ℂ e v‖ ^ 2 + ‖inner ℂ e y‖ ^ 2) / (4 * B) ≤
      coefficientDeficit M v y e t 0 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * B)).mpr
    nlinarith
  convert h using 1; ring

/-- The retained-endpoint boundary estimate loses only the source factor four. -/
lemma coefficientDeficit_one_lower {M B : ℝ} (hM : 1 < M) (hB : 0 < B)
    (v y e : H) (he : ‖e‖ = 1)
    (hone : ∀ t : ℂ, ‖t‖ ^ 2 + ‖inner ℂ e (y + t • e)‖ ^ 2 ≤
      B * coefficientDeficit M v y e t 1) (t : ℂ) :
    (1 / (4 * B)) * (‖inner ℂ e v‖ ^ 2 + ‖inner ℂ e y‖ ^ 2) ≤
      coefficientDeficit M v y e t 1 := by
  let t₁ := coefficientMinimizer M v y e 1
  have hb := hone t₁
  simp [inner_self_eq_norm_sq_to_K, he] at hb
  have henergy := minimizer_inner_energy_le (by nlinarith : 1 ≤ M ^ 2)
    (inner ℂ e v) (inner ℂ e y) t₁ (coefficientMinimizer_one_stationary hM v y e)
  have hm := coefficientDeficit_minimum_le hM v y e he t (z := 1) (by simp)
  have htotal := hb.trans (mul_le_mul_of_nonneg_left hm hB.le)
  have h : (‖inner ℂ e v‖ ^ 2 + ‖inner ℂ e y‖ ^ 2) / (4 * B) ≤
      coefficientDeficit M v y e t 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * B)).mpr
    nlinarith
  convert h using 1; ring

/-- The source boundary inequality supplies the precise uniform constants
needed by the already proved coefficient-replication theorem. -/
theorem HasBoundaryEstimate.replicationDeficits (f : Fin n → H) {M B : ℝ}
    (hM : 1 < M) (hB : 0 < B) (hf : ∀ i, ‖f i‖ = 1)
    (hb : HasBoundaryEstimate f M B) :
    HasReplicationDeficits f M (1 / (4 * B)) ((M ^ 4 + 1) / (M ^ 2 - 1)) := by
  intro a i
  let v := replicationBase f a i
  let y := replicationTail f a i
  have hzero := fun t => (hb a i t).1
  have hone := fun t => (hb a i t).2
  refine ⟨‖inner ℂ (f i) v‖ ^ 2 + ‖inner ℂ (f i) y‖ ^ 2, by positivity, ?_, ?_, ?_⟩
  · exact coefficientDeficit_zero_lower hM hB v y (f i) (hf i) hzero
  · exact coefficientDeficit_one_lower hM hB v y (f i) (hf i) hone
  · intro t z hz
    exact coefficientDeficit_interior_lower hM v y (f i) (hf i)
      (boundary_zero_tail_bound (by linarith) hB v y (f i) hzero) t hz

end ProofProject
