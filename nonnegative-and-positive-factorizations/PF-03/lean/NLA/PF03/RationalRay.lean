/-
Original mathematics and seed: Sidney Holden, Flatiron Institute,
Simons Foundation. Formalization: George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology; Codex assistance.

C08 uses a nonzero two-by-two minor and rational independence. The real scale
is never inverted, so t=0 is included without a positivity or nonzero premise.
-/
import NLA.PF03.CubicIndependence

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace NLA.PF03

theorem rational_ray_zero (C : QMat 7 3) (hC : HasNonzeroMinor C)
    (x : Fin 7 → ℚ) (t : ℝ)
    (hx : castVector x = t • (castMatrix C).mulVec alphaVector) :
    x = 0 := by
  by_contra hx0
  have hex : ∃ u : Fin 7, x u ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hx0 (funext hn)
  obtain ⟨u, hu⟩ := hex
  have hrow (r : Fin 7) : (x r : ℝ) =
      t * ((C r 0 : ℝ) + (C r 1 : ℝ) * alpha + (C r 2 : ℝ) * alpha ^ 2) := by
    have hh := congrFun hx r
    simpa [castVector, castMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      alphaVector, smul_eq_mul, add_assoc] using hh
  have hprop : ∀ r : Fin 7, ∀ k : Fin 3, x u * C r k = x r * C u k := by
    intro r
    have he : ((x u * C r 0 - x r * C u 0 : ℚ) : ℝ) +
        ((x u * C r 1 - x r * C u 1 : ℚ) : ℝ) * alpha +
        ((x u * C r 2 - x r * C u 2 : ℚ) : ℝ) * alpha ^ 2 = 0 := by
      push_cast
      rw [hrow u, hrow r]
      ring
    obtain ⟨h0, h1, h2⟩ := (cubic_eval_injective _ _ _).1 he
    intro k
    fin_cases k
    · exact sub_eq_zero.mp h0
    · exact sub_eq_zero.mp h1
    · exact sub_eq_zero.mp h2
  obtain ⟨r, s, a, b, hm⟩ := hC
  have hm0 : x u ^ 2 * (C r a * C s b - C r b * C s a) = 0 := by
    calc
      x u ^ 2 * (C r a * C s b - C r b * C s a) =
          (x u * C r a) * (x u * C s b) -
            (x u * C r b) * (x u * C s a) := by ring
      _ = (x r * C u a) * (x s * C u b) -
          (x r * C u b) * (x s * C u a) := by
        rw [hprop r a, hprop s b, hprop r b, hprop s a]
      _ = 0 := by ring
  exact hm ((mul_eq_zero.mp hm0).resolve_left (pow_ne_zero 2 hu))

#print axioms rational_ray_zero
#assert_trust kernel rational_ray_zero

end NLA.PF03
