import ProofProject.OscillatoryResolventBounds
import ProofProject.SourcePieceOperator

/-!
# Resolvent deletion and retention of the actual source pieces

All transformed-amplitude estimates are discharged. The single constant for
fixed M is chosen before Hilbert spaces, indices, positive times, signs and
resolvent rates.
-/

noncomputable section

namespace ProofProject

universe u

theorem exists_sourcePieceResolvent_bounds :
    ∀ M : ℝ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (S : BoundedSemigroup M H) (q : ℕ) (t : ℝ), 0 < t →
      ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ r : ℝ, ∀ hr : 0 < r,
        ‖S.resolventAverage r hr * S.sourcePieceOperator q t σ‖ ≤
          C * Real.exp (-sourcePieceScale q / t) *
            (r / sourcePieceLambda (q + 1) + sourcePieceScale q ^ (-1 / 4 : ℝ)) ∧
        ‖(1 - S.resolventAverage r hr) * S.sourcePieceOperator q t σ‖ ≤
          C * Real.exp (-sourcePieceScale q / t) * sourcePieceLambda q / r := by
  obtain ⟨K, hK, hres⟩ := exists_oscillatoryResolvent_bounds.{u}
  obtain ⟨A, hA, hamp⟩ := exists_sourcePieceAmplitude_weighted_bound
  intro M hM
  have hM0 : 0 ≤ M := by linarith
  let D : ℝ := (9 / 2) * K * M ^ 3 * (1 + M) * A
  let E : ℝ := 6 * M ^ 2 * A
  let F : ℝ := 4 * K * M ^ 4 * A
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let C : ℝ := 1 + D + E + F
  have hC : 0 < C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith
  have hEC : E ≤ C := by dsimp [C]; linarith
  have hFC : F ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro H _ _ _ S q t ht σ hσ r hr
  have hl : ∀ v < 2 * sourcePieceScale q, sourcePieceAmplitude q t v = 0 :=
    fun _ hv => sourcePieceAmplitude_eq_zero_of_le q t hv.le
  have hu : ∀ v, 4 * sourcePieceScale q ^ (4 / 3 : ℝ) < v →
      sourcePieceAmplitude q t v = 0 := by
    intro v hv
    apply sourcePieceAmplitude_eq_zero_of_ge q t
    simpa only [sourcePieceScale_succ] using hv.le
  have h := hres H M S (sourcePieceScale q) (A * Real.exp (-sourcePieceScale q / t))
    (sourcePieceScale_ge_sixteen q) (by positivity) (sourcePieceAmplitude q t)
    (sourcePieceAmplitude_contDiff q t) hl hu (hamp q t ht) σ hσ r hr
    (sourcePieceKernel_integrable q t σ)
  have hsqrt : Real.sqrt (sourcePieceScale q ^ (4 / 3 : ℝ)) =
      1 / sourcePieceLambda (q + 1) := by
    rw [← sourcePieceScale_succ, sourcePieceLambda_eq_inv_sqrt, one_div_one_div]
  have hpow : (2 * sourcePieceScale q) ^ (-1 / 4 : ℝ) ≤
      sourcePieceScale q ^ (-1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (sourcePieceScale_pos q)
      (by have := sourcePieceScale_pos q; linarith) (by norm_num)
  have he : 0 ≤ Real.exp (-sourcePieceScale q / t) := (Real.exp_pos _).le
  have hx : 0 ≤ r / sourcePieceLambda (q + 1) := div_nonneg hr.le (sourcePieceLambda_pos _).le
  have hy : 0 ≤ sourcePieceScale q ^ (-1 / 4 : ℝ) := Real.rpow_nonneg (sourcePieceScale_pos q).le _
  constructor
  · have hkill : ‖S.resolventAverage r hr * S.sourcePieceOperator q t σ‖ ≤
        D * Real.exp (-sourcePieceScale q / t) * (r / sourcePieceLambda (q + 1)) +
          E * Real.exp (-sourcePieceScale q / t) * (2 * sourcePieceScale q) ^ (-1 / 4 : ℝ) := by
      refine h.1.trans_eq ?_
      rw [hsqrt]
      dsimp only [D, E]
      ring
    refine hkill.trans ?_
    calc
      _ ≤ D * Real.exp (-sourcePieceScale q / t) * (r / sourcePieceLambda (q + 1)) +
          E * Real.exp (-sourcePieceScale q / t) * sourcePieceScale q ^ (-1 / 4 : ℝ) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hpow (mul_nonneg hE he)) _
      _ ≤ C * Real.exp (-sourcePieceScale q / t) * (r / sourcePieceLambda (q + 1)) +
          C * Real.exp (-sourcePieceScale q / t) * sourcePieceScale q ^ (-1 / 4 : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDC he) hx)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hEC he) hy)
      _ = _ := by ring
  · have hkeep : ‖(1 - S.resolventAverage r hr) * S.sourcePieceOperator q t σ‖ ≤
        F * Real.exp (-sourcePieceScale q / t) * sourcePieceLambda q / r := by
      refine h.2.trans_eq ?_
      rw [sourcePieceLambda_eq_inv_sqrt]
      dsimp only [F]
      ring
    exact hkeep.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hFC he)
        (sourcePieceLambda_pos q).le) hr.le)

end ProofProject
