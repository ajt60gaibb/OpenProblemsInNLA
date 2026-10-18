import NLA.Proofs.TR14.GL2AffineChartPolynomial

/-!
The exact nonzero affine coordinate of the audited binary chart. This is an
evaluation identity only; root multiplicities and the point at infinity are
separate obligations.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open scoped BigOperators
open Polynomial
noncomputable section

/-- The chart acts on nonzero affine coordinates by `t ↦ z + t⁻¹`, with the
ambient homogeneous degree retained even when the affine degree drops. -/
theorem chart_dehomogenize_eval_nonzero
    (z : ℂ) (d : ℕ) (g : Fin (d + 1) → ℂ)
    (t : ℂ) (ht : t ≠ 0) :
    (dehomogenize d (transportedApolarVector z d g)).eval t =
      t ^ d * (dehomogenize d g).eval (z + t⁻¹) := by
  have hlinear : 1 + z * t = t * (z + t⁻¹) := by
    field_simp [ht]
    ring
  have hterm (i : Fin (d + 1)) :
      g i * t ^ (d - i.val) * (1 + z * t) ^ i.val =
        t ^ d * (g i * (z + t⁻¹) ^ i.val) := by
    have hi : i.val ≤ d := Nat.le_of_lt_succ i.isLt
    have hexp : t ^ (d - i.val) * t ^ i.val = t ^ d := by
      rw [← pow_add, Nat.sub_add_cancel hi]
    calc
      g i * t ^ (d - i.val) * (1 + z * t) ^ i.val =
          g i * t ^ (d - i.val) *
            (t ^ i.val * (z + t⁻¹) ^ i.val) := by
              rw [hlinear, mul_pow]
      _ = (t ^ (d - i.val) * t ^ i.val) *
            (g i * (z + t⁻¹) ^ i.val) := by ring
      _ = t ^ d * (g i * (z + t⁻¹) ^ i.val) := by rw [hexp]
  calc
    (dehomogenize d (transportedApolarVector z d g)).eval t =
        ∑ i : Fin (d + 1),
          g i * t ^ (d - i.val) * (1 + z * t) ^ i.val := by
            rw [dehomogenize_transportedApolarVector]
            simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
              Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
              Polynomial.eval_add, Polynomial.eval_one]
    _ = ∑ i : Fin (d + 1),
          t ^ d * (g i * (z + t⁻¹) ^ i.val) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hterm i
    _ = t ^ d * (dehomogenize d g).eval (z + t⁻¹) := by
          rw [dehomogenize_eval, Finset.mul_sum]

#assert_trust kernel chart_dehomogenize_eval_nonzero
#print axioms chart_dehomogenize_eval_nonzero

end
end NLA.Proofs.TR14
