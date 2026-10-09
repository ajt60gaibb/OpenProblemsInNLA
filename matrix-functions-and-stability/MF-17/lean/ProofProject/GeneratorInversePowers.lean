import ProofProject.GammaResolventPowers
import ProofProject.RescaledResolventInverse

/-!
# Gamma representation and uniform bounds for powers of the generator inverse

The full strong-generator inverse is the negative rescaled resolvent average.
Its positive powers therefore inherit the normalized gamma representation and
the original semigroup bound, with no growth in the power.
-/

noncomputable section

namespace ProofProject

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {T : StableSemigroup M H} {B : H →L[ℂ] H}

/-- This representation uses the original full-generator inverse and the
actual bounded time rescaling, for every positive time parameter. -/
theorem IsGeneratorInverse.neg_pow_succ_eq_gammaOperator (hB : IsGeneratorInverse T B)
    (n : ℕ) (t : ℝ) (ht : 0 < t) :
    (-B) ^ (n + 1) =
      (BoundedSemigroup.ofStableRescale T t ht).kernelOperator (gammaKernel n (1 / t))
        (gammaKernel_integrable n (one_div_pos.mpr ht)) := by
  rw [← hB.resolventAverage_ofStableRescale t ht]
  exact (BoundedSemigroup.ofStableRescale T t ht).resolventAverage_pow_succ_eq_kernelOperator
    n (1 / t) (one_div_pos.mpr ht)

/-- Every positive power of the inverse retains the original semigroup bound. -/
theorem IsGeneratorInverse.pow_succ_norm_le (hB : IsGeneratorInverse T B) (n : ℕ) :
    ‖B ^ (n + 1)‖ ≤ M := by
  have h := (BoundedSemigroup.ofStableRescale T 1 zero_lt_one).resolventAverage_pow_succ_norm_le
    n (1 / 1) (one_div_pos.mpr zero_lt_one)
  rw [hB.resolventAverage_ofStableRescale 1 zero_lt_one] at h
  rcases Nat.even_or_odd (n + 1) with hn | hn
  · simpa only [hn.neg_pow] using h
  · simpa only [hn.neg_pow, norm_neg] using h

end ProofProject
