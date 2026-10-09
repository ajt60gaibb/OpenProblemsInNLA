import NLA.Proofs.RA06.GraphCounting
import Mathlib.Analysis.MeanInequalitiesPow

/-! The two-edge real-power inequality behind complete-graph sensitivities. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RA06

/-- Convexity of `t ↦ t^p` bounds one edge by two legs through a third vertex. -/
theorem abs_sub_rpow_le_two_legs
    (p a b c : ℝ) (hp : 1 ≤ p) :
    Real.rpow |a - b| p ≤
      Real.rpow 2 (p - 1) *
        (Real.rpow |a - c| p + Real.rpow |b - c| p) := by
  have htriangle : |a - b| ≤ |a - c| + |b - c| := by
    calc
      |a - b| = |(a - c) + (c - b)| := by congr 1; ring
      _ ≤ |a - c| + |c - b| := abs_add_le _ _
      _ = |a - c| + |b - c| := by rw [abs_sub_comm c b]
  have hmon : Real.rpow |a - b| p ≤
      Real.rpow (|a - c| + |b - c|) p := by
    simpa only [Real.rpow_eq_pow] using
      Real.rpow_le_rpow (abs_nonneg _) htriangle (by linarith : 0 ≤ p)
  let u : NNReal := ⟨|a - c|, abs_nonneg _⟩
  let v : NNReal := ⟨|b - c|, abs_nonneg _⟩
  have hconv := NNReal.rpow_add_le_mul_rpow_add_rpow u v hp
  have hreal : Real.rpow (|a - c| + |b - c|) p ≤
      Real.rpow 2 (p - 1) *
        (Real.rpow |a - c| p + Real.rpow |b - c| p) := by
    exact_mod_cast hconv
  exact hmon.trans hreal

#print axioms abs_sub_rpow_le_two_legs

end NLA.Proofs.RA06
