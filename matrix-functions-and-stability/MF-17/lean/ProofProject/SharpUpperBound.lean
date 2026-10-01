import ProofProject.InverseExponentialKernel
import ProofProject.SourceBesselRemainder
import ProofProject.OscillatoryTailBound

/-!
# The sharp upper bound for the actual inverse exponential

The exact Bessel representation decomposes into the two proved oscillatory
tails and one fixed L¹ remainder. All constants are selected before the
Hilbert space, generator and time, and the original bound `M` is preserved.
-/

noncomputable section

open MeasureTheory

namespace ProofProject

universe u

/-- A uniform bound at every positive time for inverses of the full strong
generator on arbitrary complete complex Hilbert spaces. -/
theorem exists_inverseEvolution_sharp_upper :
    ∀ M : ℝ, 1 < M → ∃ C : ℝ, 0 < C ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (T : StableSemigroup M H) (B : H →L[ℂ] H), IsGeneratorInverse T B →
      ∀ t : ℝ, 0 < t → ‖inverseEvolution B t‖ ≤ C * growthLog t ^ growthExponent M := by
  intro M hM
  have hM0 : 0 ≤ M := by linarith
  obtain ⟨Cosc, hCosc, hosc⟩ := exists_sourceOscillatoryTail_growth_bound.{u} M hM
  obtain ⟨cPlus, cMinus, h, hi, hz, hdecomp⟩ := exists_bessel_tail_decomposition
  let I := ∫ u : ℝ, ‖h u‖
  have hI : 0 ≤ I := integral_nonneg (fun _ => norm_nonneg _)
  let C := 1 + (‖cPlus‖ + ‖cMinus‖) * Cosc + M * I
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro H _ _ _ T B hB t ht
  let S := BoundedSemigroup.ofStableRescale T t ht
  have hd := dampedRemainder_integrable hi hz ht
  have hkernel : S.kernelOperator (besselDampedKernel t) (besselDampedKernel_integrable ht) =
      cPlus • S.sourceOscillatoryTailOperator t 1 ht +
        cMinus • S.sourceOscillatoryTailOperator t (-1) ht +
          S.kernelOperator (dampedRemainder h t) hd := by
    ext x
    simp only [BoundedSemigroup.sourceOscillatoryTailOperator,
      BoundedSemigroup.kernelOperator_apply, add_apply, smul_apply]
    have hplus := S.kernelOrbit_integrable (sourceOscillatoryTailKernel_integrable ht 1) x
    have hminus := S.kernelOrbit_integrable (sourceOscillatoryTailKernel_integrable ht (-1)) x
    have hrest := S.kernelOrbit_integrable hd x
    calc
      _ = ∫ u, (cPlus * sourceOscillatoryTailKernel t 1 u +
          cMinus * sourceOscillatoryTailKernel t (-1) u + dampedRemainder h t u) •
            S.positiveOrbit x u := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun u => congrArg (fun z : ℂ => z • S.positiveOrbit x u)
          (hdecomp t ht u)
      _ = _ := by
        simp only [add_smul, mul_smul]
        have hadd := integral_add ((hplus.smul cPlus).add (hminus.smul cMinus)) hrest
        have hpair := integral_add (hplus.smul cPlus) (hminus.smul cMinus)
        simp only [Pi.add_apply, Pi.smul_apply, integral_smul] at hadd hpair
        rw [hpair] at hadd
        exact hadd
  have hrest : ‖S.kernelOperator (dampedRemainder h t) hd‖ ≤ M * I :=
    (S.kernelOperator_norm_le _ hd).trans
      (mul_le_mul_of_nonneg_left (integral_norm_dampedRemainder_le hi hz ht) (by linarith))
  have hp := hosc H S t ht 1 (Or.inl rfl)
  have hm := hosc H S t ht (-1) (Or.inr rfl)
  have hL : 1 ≤ growthLog t ^ growthExponent M :=
    Real.one_le_rpow (one_le_growthLog ht.le) (growthExponent_nonneg M)
  rw [hB.inverseEvolution_eq_one_sub_besselKernelOperator t ht, hkernel]
  calc
    _ ≤ ‖(1 : H →L[ℂ] H)‖ + ‖cPlus • S.sourceOscillatoryTailOperator t 1 ht +
        cMinus • S.sourceOscillatoryTailOperator t (-1) ht +
          S.kernelOperator (dampedRemainder h t) hd‖ := norm_sub_le _ _
    _ ≤ 1 + (‖cPlus‖ * ‖S.sourceOscillatoryTailOperator t 1 ht‖ +
        ‖cMinus‖ * ‖S.sourceOscillatoryTailOperator t (-1) ht‖ + M * I) := by
      apply add_le_add ContinuousLinearMap.norm_id_le
      apply (norm_add_le _ _).trans
      apply add_le_add _ hrest
      simpa only [norm_smul] using norm_add_le
        (cPlus • S.sourceOscillatoryTailOperator t 1 ht)
        (cMinus • S.sourceOscillatoryTailOperator t (-1) ht)
    _ ≤ 1 + ((‖cPlus‖ + ‖cMinus‖) * Cosc *
        growthLog t ^ growthExponent M + M * I) := by
      nlinarith [mul_le_mul_of_nonneg_left hp (norm_nonneg cPlus),
        mul_le_mul_of_nonneg_left hm (norm_nonneg cMinus)]
    _ ≤ C * growthLog t ^ growthExponent M := by
      dsimp [C]
      nlinarith [mul_le_mul_of_nonneg_left hL (mul_nonneg (by linarith : 0 ≤ M) hI)]

end ProofProject
