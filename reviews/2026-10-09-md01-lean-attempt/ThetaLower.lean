import Target
import GraphLower

open MeasureTheory Matrix unitInterval

namespace MD01FullBridge

private theorem theta_nonneg_pos {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    0 ≤ MD01Scratch.theta G := by
  obtain ⟨X, hX, _, _, htheta⟩ := MD01Scratch.theta_max_attained hn G
  have hq := hX.dotProduct_mulVec_nonneg (fun _ : Fin n => (1 : ℝ))
  simp only [Pi.star_apply, star_one, dotProduct, Matrix.mulVec, one_mul] at hq
  simpa [htheta] using hq

theorem theta_nonneg (n : ℕ) (G : SimpleGraph (Fin n)) :
    0 ≤ MD01Scratch.theta G := by
  by_cases hn : 0 < n
  · exact theta_nonneg_pos hn G
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [MD01Scratch.theta, Matrix.trace]

/-- The exact lower expectation bound follows from the Lovász theta complement
product inequality, which is an explicit premise here. -/
theorem theta_expectation_lower_from_product (n : ℕ)
    (hprod : ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ≤ MD01Scratch.theta G * MD01Scratch.theta Gᶜ) :
    Real.sqrt n ≤ ∫ G : SimpleGraph (Fin n), MD01Scratch.theta G ∂
      (SimpleGraph.binomialRandom (Fin n) (⟨(1 / 2 : ℝ), by norm_num⟩ : I)) := by
  simpa [graphMeasure, half] using
    graph_expectation_lower_from_product n (fun G => MD01Scratch.theta G)
      (theta_nonneg n) hprod

#print axioms theta_nonneg
#print axioms theta_expectation_lower_from_product

end MD01FullBridge
