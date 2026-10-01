import ProofProject.ResolventAverage
import ProofProject.InverseGenerator
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The rescaled normalized average is the negative generator inverse

This identity is a strong change of variables in the already constructed
Laplace integral. It does not assign a generator to the bounded rescaling.
-/

noncomputable section

namespace ProofProject

open MeasureTheory Set

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Exponential damping cancels exactly, and the positive Jacobian supplies
precisely the negative of the original strong Laplace inverse. -/
theorem StableSemigroup.resolventAverage_ofStableRescale (T : StableSemigroup M H)
    (t : ℝ) (ht : 0 < t) :
    (BoundedSemigroup.ofStableRescale T t ht).resolventAverage (1 / t) (one_div_pos.mpr ht) =
      -T.laplaceInverse := by
  ext x
  rw [BoundedSemigroup.resolventAverage_apply]
  change (∫ u : ℝ in Ioi 0, (((1 / t) * Real.exp (-(1 / t) * u) : ℝ) : ℂ) •
    ((Real.exp (u / t) : ℂ) • T.op (u / t) x)) =
      -(-(∫ s : ℝ in Ioi 0, T.op s x))
  rw [neg_neg]
  have heq (u : ℝ) :
      (((1 / t) * Real.exp (-(1 / t) * u) : ℝ) : ℂ) •
        ((Real.exp (u / t) : ℂ) • T.op (u / t) x) =
      (1 / t : ℝ) • T.op (u / t) x := by
    rw [smul_smul, ← Complex.ofReal_mul]
    have he : ((1 / t) * Real.exp (-(1 / t) * u)) * Real.exp (u / t) = 1 / t := by
      rw [mul_assoc, ← Real.exp_add, show -(1 / t) * u + u / t = 0 by ring,
        Real.exp_zero, mul_one]
    rw [he]
    exact_mod_cast (RCLike.real_smul_eq_coe_smul (K := ℂ) (1 / t : ℝ) (T.op (u / t) x)).symm
  simp_rw [heq]
  rw [integral_smul]
  have h := integral_comp_mul_right_Ioi' (fun s : ℝ => T.op s x) (0 : ℝ)
    (one_div_pos.mpr ht)
  simpa only [zero_mul, div_eq_mul_inv, one_div, one_mul] using h

/-- Any inverse of the full generator has the same rescaled-average identity. -/
theorem IsGeneratorInverse.resolventAverage_ofStableRescale
    {T : StableSemigroup M H} {B : H →L[ℂ] H} (hB : IsGeneratorInverse T B)
    (t : ℝ) (ht : 0 < t) :
    (BoundedSemigroup.ofStableRescale T t ht).resolventAverage (1 / t) (one_div_pos.mpr ht) = -B := by
  rw [hB.eq_laplaceInverse]
  exact T.resolventAverage_ofStableRescale t ht

end ProofProject
