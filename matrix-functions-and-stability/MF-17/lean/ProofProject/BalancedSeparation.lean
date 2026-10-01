import ProofProject.BalancedOperatorFactors
import ProofProject.ApproximateSynthesis

/-!
# Transfer of commuting separators to balanced factors

The source controls sums of square roots of errors on the original pieces.
The two Gram identities transfer that same sum to both factor families, with
only the uniform factor `sqrt (M + 1)`. No dimension factor is introduced.
-/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {n : ℕ}

/-- The source's square-root error budget for one ordered cut. -/
def sqrtSeparationError (B : Fin n → H →L[ℂ] H) (R : H →L[ℂ] H) (k : ℕ) : ℝ :=
  ∑ j, Real.sqrt (if k ≤ j.val then ‖(ContinuousLinearMap.id ℂ H - R).comp (B j)‖
    else ‖R.comp (B j)‖)

omit [CompleteSpace H] in
lemma sqrtSeparationError_nonneg (B : Fin n → H →L[ℂ] H)
    (R : H →L[ℂ] H) (k : ℕ) : 0 ≤ sqrtSeparationError B R k :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

private lemma balanced_right_norm_le {B Y S : H →L[ℂ] H} {L : ℝ}
    (hY : Y * star Y = CFC.abs (star B)) (hS : ‖S‖ ≤ L) :
    ‖S * Y‖ ≤ Real.sqrt L * Real.sqrt ‖S * B‖ := by
  have hL : 0 ≤ L := (norm_nonneg S).trans hS
  rw [← Real.sqrt_mul hL]
  exact Real.le_sqrt_of_sq_le ((balancedFactor_right_separator hY S).trans
    (mul_le_mul_of_nonneg_right hS (norm_nonneg _)))

private lemma balanced_left_norm_le {B X S : H →L[ℂ] H} {L : ℝ}
    (hX : star X * X = CFC.abs B) (hS : ‖S‖ ≤ L) :
    ‖star S * star X‖ ≤ Real.sqrt L * Real.sqrt ‖B * S‖ := by
  have hL : 0 ≤ L := (norm_nonneg S).trans hS
  rw [← Real.sqrt_mul hL]
  exact Real.le_sqrt_of_sq_le ((balancedFactor_left_separator hX S).trans
    (mul_le_mul_of_nonneg_right hS (norm_nonneg _)))

/-- The right factors use the original separator. -/
theorem balancedFactors_right_separationError_le
    (B Y : Fin n → H →L[ℂ] H)
    (hY : ∀ j, Y j * star (Y j) = CFC.abs (star (B j)))
    (R : H →L[ℂ] H) {M : ℝ} (hR : ‖R‖ ≤ M) (k : ℕ) :
    separationError Y R k ≤ Real.sqrt (M + 1) * sqrtSeparationError B R k := by
  have hR' : ‖R‖ ≤ M + 1 := by linarith
  have hI : ‖ContinuousLinearMap.id ℂ H - R‖ ≤ M + 1 :=
    (norm_sub_le _ _).trans (by linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := H)])
  unfold separationError sqrtSeparationError
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  split_ifs with hk
  · exact balanced_right_norm_le (hY j) hI
  · exact balanced_right_norm_le (hY j) hR'

/-- The adjoints of the left factors use the adjoint separator. Commutation
is needed only to identify the right-sided piece errors with the same budget. -/
theorem balancedFactors_left_separationError_le
    (B X : Fin n → H →L[ℂ] H)
    (hX : ∀ j, star (X j) * X j = CFC.abs (B j))
    (R : H →L[ℂ] H) {M : ℝ} (hR : ‖R‖ ≤ M)
    (hcomm : ∀ j, Commute R (B j)) (k : ℕ) :
    separationError (fun j => (X j).adjoint) R.adjoint k ≤
      Real.sqrt (M + 1) * sqrtSeparationError B R k := by
  have hR' : ‖R‖ ≤ M + 1 := by linarith
  have hI : ‖ContinuousLinearMap.id ℂ H - R‖ ≤ M + 1 :=
    (norm_sub_le _ _).trans (by linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := H)])
  unfold separationError sqrtSeparationError
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  split_ifs with hk
  · have heq : B j * (1 - R) = (1 - R) * B j := by
      rw [mul_sub, sub_mul, mul_one, one_mul, (hcomm j).eq]
    have h := balanced_left_norm_le (hX j) hI
    change ‖star (1 - R) * star (X j)‖ ≤
      Real.sqrt (M + 1) * Real.sqrt ‖B j * (1 - R)‖ at h
    rw [heq] at h
    change ‖(1 - star R) * star (X j)‖ ≤
      Real.sqrt (M + 1) * Real.sqrt ‖(1 - R) * B j‖
    simpa only [star_sub, star_one] using h
  · have h := balanced_left_norm_le (hX j) hR'
    change ‖star R * star (X j)‖ ≤ Real.sqrt (M + 1) * Real.sqrt ‖R * B j‖
    simpa only [(hcomm j).eq] using h

/-- One commuting family of piece separators supplies both factor families.
The hypothesis is the actual square-root error budget, chosen before the cut. -/
theorem balancedFactors_hasApproximateSeparators
    (B X Y : Fin n → H →L[ℂ] H)
    (hX : ∀ j, star (X j) * X j = CFC.abs (B j))
    (hY : ∀ j, Y j * star (Y j) = CFC.abs (star (B j)))
    {M ε : ℝ}
    (hsep : ∀ k : ℕ, 0 < k → k < n → ∃ R : H →L[ℂ] H,
      ‖R‖ ≤ M ∧ (∀ j, Commute R (B j)) ∧
      Real.sqrt (M + 1) * sqrtSeparationError B R k ≤ ε) :
    HasApproximateSeparators (fun j => (X j).adjoint) M ε ∧
      HasApproximateSeparators Y M ε := by
  constructor
  · intro k hk0 hkn
    obtain ⟨R, hR, hcomm, herr⟩ := hsep k hk0 hkn
    refine ⟨R.adjoint, ?_, (balancedFactors_left_separationError_le B X hX R hR hcomm k).trans herr⟩
    change ‖star R‖ ≤ M
    simpa only [norm_star] using hR
  · intro k hk0 hkn
    obtain ⟨R, hR, hcomm, herr⟩ := hsep k hk0 hkn
    exact ⟨R, hR, (balancedFactors_right_separationError_le B Y hY R hR k).trans herr⟩

end ProofProject
