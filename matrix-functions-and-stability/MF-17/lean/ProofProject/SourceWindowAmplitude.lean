import ProofProject.SourceWindowRescaling
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Derivatives and fixed cutoff bounds for the actual source amplitude

The first two scaled derivatives include every chain-rule power of `N` and
every cutoff term. The fixed cutoff and its first two derivatives share one
global bound. Strict containment of its closed support makes every derivative
of the scaled amplitude vanish at both integration endpoints.
-/

noncomputable section

open Set
open scoped ContDiff

namespace ProofProject

theorem sourceTriangleCutoff_deriv_contDiff :
    ContDiff ℝ ∞ (deriv sourceTriangleCutoff) :=
  (contDiff_infty_iff_deriv.mp sourceTriangleCutoff_contDiff).2

theorem sourceTriangleCutoff_second_contDiff :
    ContDiff ℝ ∞ (deriv (deriv sourceTriangleCutoff)) :=
  (contDiff_infty_iff_deriv.mp sourceTriangleCutoff_deriv_contDiff).2

theorem sourceTriangleCutoff_hasDerivAt (w : ℝ) :
    HasDerivAt sourceTriangleCutoff (deriv sourceTriangleCutoff w) w :=
  ((contDiff_infty_iff_deriv.mp sourceTriangleCutoff_contDiff).1 w).hasDerivAt

theorem sourceTriangleCutoff_deriv_hasDerivAt (w : ℝ) :
    HasDerivAt (deriv sourceTriangleCutoff) (deriv (deriv sourceTriangleCutoff) w) w :=
  ((contDiff_infty_iff_deriv.mp sourceTriangleCutoff_deriv_contDiff).1 w).hasDerivAt

/-- One fixed constant bounds the actual cutoff and its first two derivatives
at every real point, independently of all source parameters. -/
theorem exists_sourceTriangleCutoff_derivative_bound :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ w : ℝ, ‖sourceTriangleCutoff w‖ ≤ D ∧
      ‖deriv sourceTriangleCutoff w‖ ≤ D ∧
      ‖deriv (deriv sourceTriangleCutoff) w‖ ≤ D := by
  obtain ⟨D₁, hD₁⟩ := sourceTriangleCutoff_hasCompactSupport.deriv.exists_bound_of_continuous
    sourceTriangleCutoff_deriv_contDiff.continuous
  obtain ⟨D₂, hD₂⟩ := sourceTriangleCutoff_hasCompactSupport.deriv.deriv.exists_bound_of_continuous
    sourceTriangleCutoff_second_contDiff.continuous
  refine ⟨max 1 (max D₁ D₂), le_max_left _ _, fun w => ?_⟩
  exact ⟨(sourceTriangleCutoff_norm_le_one w).trans (le_max_left _ _),
    (hD₁ w).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (hD₂ w).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

private theorem tsupport_iterate_deriv_subset (f : ℝ → ℂ) (n : ℕ) :
    tsupport (deriv^[n] f) ⊆ tsupport f := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact tsupport_deriv_subset.trans ih

/-- The strict support inclusion gives zero values for every cutoff derivative
outside the open integration interval, including its two endpoints. -/
theorem sourceTriangleCutoff_iteratedDeriv_eq_zero (n : ℕ) {w : ℝ}
    (hw : w ≤ 1 / 2 ∨ 7 / 2 ≤ w) : (deriv^[n] sourceTriangleCutoff) w = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have hm := sourceTriangleCutoff_tsupport_subset
    (tsupport_iterate_deriv_subset sourceTriangleCutoff n h)
  rcases hw with hw | hw <;> linarith [hm.1, hm.2]

/-- The first scaled derivative, for specified values of the original derivative. -/
def sourceWindowAmplitudeFirst (N : ℝ) (a a' : ℝ → ℂ) (j : ℕ) (w : ℝ) : ℂ :=
  (N : ℂ) ^ 2 * a' (N * ((j : ℝ) + w)) * sourceTriangleCutoff w +
    (N : ℂ) * a (N * ((j : ℝ) + w)) * deriv sourceTriangleCutoff w

/-- The second scaled derivative contains the two identical mixed terms. -/
def sourceWindowAmplitudeSecond (N : ℝ) (a a' a'' : ℝ → ℂ) (j : ℕ) (w : ℝ) : ℂ :=
  (N : ℂ) ^ 3 * a'' (N * ((j : ℝ) + w)) * sourceTriangleCutoff w +
    2 * (N : ℂ) ^ 2 * a' (N * ((j : ℝ) + w)) * deriv sourceTriangleCutoff w +
      (N : ℂ) * a (N * ((j : ℝ) + w)) * deriv (deriv sourceTriangleCutoff) w

private theorem sourceWindowArgument_hasDerivAt (N : ℝ) (j : ℕ) (w : ℝ) :
    HasDerivAt (fun v : ℝ => N * ((j : ℝ) + v)) N w := by
  simpa only [mul_one] using! ((hasDerivAt_id w).const_add (j : ℝ)).const_mul N

/-- The first chain-rule formula uses only differentiability at the actual
rescaled point; positivity of `N` is not needed for this identity. -/
theorem sourceWindowAmplitude_hasDerivAt (N : ℝ) {a a' : ℝ → ℂ} (j : ℕ) (w : ℝ)
    (ha : HasDerivAt a (a' (N * ((j : ℝ) + w))) (N * ((j : ℝ) + w))) :
    HasDerivAt (sourceWindowAmplitude N a j) (sourceWindowAmplitudeFirst N a a' j w) w := by
  have hcomp := ha.scomp w (sourceWindowArgument_hasDerivAt N j w)
  convert! ((hcomp.const_mul (N : ℂ)).mul (sourceTriangleCutoff_hasDerivAt w)) using 1
  all_goals first | rfl |
    (simp only [sourceWindowAmplitudeFirst, Function.comp_apply, Complex.real_smul]; ring)

/-- The second chain-rule formula, with both mixed cutoff terms combined. -/
theorem sourceWindowAmplitudeFirst_hasDerivAt (N : ℝ) {a a' a'' : ℝ → ℂ} (j : ℕ) (w : ℝ)
    (ha : HasDerivAt a (a' (N * ((j : ℝ) + w))) (N * ((j : ℝ) + w)))
    (ha' : HasDerivAt a' (a'' (N * ((j : ℝ) + w))) (N * ((j : ℝ) + w))) :
    HasDerivAt (sourceWindowAmplitudeFirst N a a' j)
      (sourceWindowAmplitudeSecond N a a' a'' j w) w := by
  have hcomp := ha.scomp w (sourceWindowArgument_hasDerivAt N j w)
  have hcomp' := ha'.scomp w (sourceWindowArgument_hasDerivAt N j w)
  convert! (((hcomp'.const_mul ((N : ℂ) ^ 2)).mul (sourceTriangleCutoff_hasDerivAt w)).add
    ((hcomp.const_mul (N : ℂ)).mul (sourceTriangleCutoff_deriv_hasDerivAt w))) using 1
  all_goals first | rfl |
    (simp only [sourceWindowAmplitudeSecond, Function.comp_apply, Complex.real_smul]; ring)

/-- The actual derivative is the explicit first chain-rule expression. -/
theorem deriv_sourceWindowAmplitude (N : ℝ) {a : ℝ → ℂ}
    (ha : Differentiable ℝ a) (j : ℕ) :
    deriv (sourceWindowAmplitude N a j) = sourceWindowAmplitudeFirst N a (deriv a) j := by
  funext w
  exact (sourceWindowAmplitude_hasDerivAt N j w (ha _).hasDerivAt).deriv

/-- The actual second derivative is the explicit second chain-rule expression. -/
theorem deriv_twice_sourceWindowAmplitude (N : ℝ) {a : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) (j : ℕ) :
    deriv (deriv (sourceWindowAmplitude N a j)) =
      sourceWindowAmplitudeSecond N a (deriv a) (deriv (deriv a)) j := by
  have hd := (contDiff_infty_iff_deriv.mp ha).1
  have hd' := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp ha).2).1
  rw [deriv_sourceWindowAmplitude N hd j]
  funext w
  exact (sourceWindowAmplitudeFirst_hasDerivAt N j w (hd _).hasDerivAt (hd' _).hasDerivAt).deriv

/-- Every iterated derivative of the actual scaled amplitude vanishes at both
integration endpoints. The support argument needs no global regularity of `a`. -/
theorem sourceWindowAmplitude_iteratedDeriv_eq_zero (N : ℝ) (a : ℝ → ℂ) (j n : ℕ)
    {w : ℝ} (hw : w ≤ 1 / 2 ∨ 7 / 2 ≤ w) :
    (deriv^[n] (sourceWindowAmplitude N a j)) w = 0 := by
  have hs : tsupport (sourceWindowAmplitude N a j) ⊆ tsupport sourceTriangleCutoff :=
    tsupport_mul_subset_right
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have hm := sourceTriangleCutoff_tsupport_subset
    (hs (tsupport_iterate_deriv_subset (sourceWindowAmplitude N a j) n h))
  rcases hw with hw | hw <;> linarith [hm.1, hm.2]

@[simp] theorem sourceWindowAmplitude_iteratedDeriv_left (N : ℝ) (a : ℝ → ℂ) (j n : ℕ) :
    (deriv^[n] (sourceWindowAmplitude N a j)) (1 / 2) = 0 :=
  sourceWindowAmplitude_iteratedDeriv_eq_zero N a j n (Or.inl le_rfl)

@[simp] theorem sourceWindowAmplitude_iteratedDeriv_right (N : ℝ) (a : ℝ → ℂ) (j n : ℕ) :
    (deriv^[n] (sourceWindowAmplitude N a j)) (7 / 2) = 0 :=
  sourceWindowAmplitude_iteratedDeriv_eq_zero N a j n (Or.inr le_rfl)

theorem sourceWindowAmplitudeFirst_eq_zero (N : ℝ) (a a' : ℝ → ℂ) (j : ℕ)
    {w : ℝ} (hw : w ≤ 1 / 2 ∨ 7 / 2 ≤ w) :
    sourceWindowAmplitudeFirst N a a' j w = 0 := by
  have hz := sourceTriangleCutoff_iteratedDeriv_eq_zero 0 hw
  have hz' := sourceTriangleCutoff_iteratedDeriv_eq_zero 1 hw
  simp only [Function.iterate_zero_apply] at hz
  simp only [Function.iterate_one] at hz'
  simp only [sourceWindowAmplitudeFirst, hz, hz', mul_zero, add_zero]

theorem sourceWindowAmplitudeSecond_eq_zero (N : ℝ) (a a' a'' : ℝ → ℂ) (j : ℕ)
    {w : ℝ} (hw : w ≤ 1 / 2 ∨ 7 / 2 ≤ w) :
    sourceWindowAmplitudeSecond N a a' a'' j w = 0 := by
  have hz := sourceTriangleCutoff_iteratedDeriv_eq_zero 0 hw
  have hz' := sourceTriangleCutoff_iteratedDeriv_eq_zero 1 hw
  have hz'' := sourceTriangleCutoff_iteratedDeriv_eq_zero 2 hw
  simp only [Function.iterate_zero_apply] at hz
  simp only [Function.iterate_one] at hz'
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at hz''
  simp only [sourceWindowAmplitudeSecond, hz, hz', hz'', mul_zero, add_zero]

/-- A direct pointwise bound, retaining the exact chain-rule scaling. -/
theorem norm_sourceWindowAmplitudeFirst_le {N D : ℝ} (hN : 0 ≤ N)
    (a a' : ℝ → ℂ) (j : ℕ) (w : ℝ) (hD : ‖deriv sourceTriangleCutoff w‖ ≤ D) :
    ‖sourceWindowAmplitudeFirst N a a' j w‖ ≤
      N ^ 2 * ‖a' (N * ((j : ℝ) + w))‖ +
        N * ‖a (N * ((j : ℝ) + w))‖ * D := by
  calc
    _ ≤ ‖(N : ℂ) ^ 2 * a' (N * ((j : ℝ) + w)) * sourceTriangleCutoff w‖ +
        ‖(N : ℂ) * a (N * ((j : ℝ) + w)) * deriv sourceTriangleCutoff w‖ := norm_add_le _ _
    _ = N ^ 2 * ‖a' (N * ((j : ℝ) + w))‖ * ‖sourceTriangleCutoff w‖ +
        N * ‖a (N * ((j : ℝ) + w))‖ * ‖deriv sourceTriangleCutoff w‖ := by
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hN]
    _ ≤ _ := add_le_add
      (mul_le_of_le_one_right (mul_nonneg (sq_nonneg _) (norm_nonneg _))
        (sourceTriangleCutoff_norm_le_one w))
      (mul_le_mul_of_nonneg_left hD (mul_nonneg hN (norm_nonneg _)))

/-- The second-derivative bound preserves the middle factor `2`. -/
theorem norm_sourceWindowAmplitudeSecond_le {N D : ℝ} (hN : 0 ≤ N)
    (a a' a'' : ℝ → ℂ) (j : ℕ) (w : ℝ)
    (hD' : ‖deriv sourceTriangleCutoff w‖ ≤ D)
    (hD'' : ‖deriv (deriv sourceTriangleCutoff) w‖ ≤ D) :
    ‖sourceWindowAmplitudeSecond N a a' a'' j w‖ ≤
      N ^ 3 * ‖a'' (N * ((j : ℝ) + w))‖ +
        2 * N ^ 2 * ‖a' (N * ((j : ℝ) + w))‖ * D +
          N * ‖a (N * ((j : ℝ) + w))‖ * D := by
  calc
    _ ≤ (‖(N : ℂ) ^ 3 * a'' (N * ((j : ℝ) + w)) * sourceTriangleCutoff w‖ +
        ‖2 * (N : ℂ) ^ 2 * a' (N * ((j : ℝ) + w)) * deriv sourceTriangleCutoff w‖) +
        ‖(N : ℂ) * a (N * ((j : ℝ) + w)) * deriv (deriv sourceTriangleCutoff) w‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (N ^ 3 * ‖a'' (N * ((j : ℝ) + w))‖ * ‖sourceTriangleCutoff w‖ +
        2 * N ^ 2 * ‖a' (N * ((j : ℝ) + w))‖ * ‖deriv sourceTriangleCutoff w‖) +
        N * ‖a (N * ((j : ℝ) + w))‖ * ‖deriv (deriv sourceTriangleCutoff) w‖ := by
      norm_num only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hN, Complex.norm_ofNat]
    _ ≤ _ := add_le_add (add_le_add
      (mul_le_of_le_one_right (mul_nonneg (pow_nonneg hN _) (norm_nonneg _))
        (sourceTriangleCutoff_norm_le_one w))
      (mul_le_mul_of_nonneg_left hD' (by positivity)))
      (mul_le_mul_of_nonneg_left hD'' (mul_nonneg hN (norm_nonneg _)))

end ProofProject
