import ProofProject.PowerIntegralBounds

/-!
# Integrable angular power majorants

Singularities of order less than one are integrable at the center and at both
endpoints of a symmetric angular interval. The bases are explicitly
nonnegative on the interval. The assigned values at the finitely many singular
points are real values and do not affect Lebesgue integrability.
-/

noncomputable section

open MeasureTheory

namespace ProofProject

/-- A central absolute-power singularity of order less than one is integrable
on every symmetric interval of positive radius. -/
theorem intervalIntegrable_abs_singular_power {a R : ℝ} (ha : a < 1) (hR : 0 < R) :
    IntervalIntegrable (fun θ : ℝ => |θ| ^ (-a)) volume (-R) R := by
  have hp := intervalIntegrable_singular_power ha R
  have hpos : IntervalIntegrable (fun θ : ℝ => |θ| ^ (-a)) volume 0 R := by
    apply hp.congr
    intro θ hθ
    rw [Set.uIoc_of_le hR.le] at hθ
    simp only [abs_of_nonneg hθ.1.le]
  have hn : IntervalIntegrable (fun θ : ℝ => (-θ) ^ (-a)) volume (-R) 0 := by
    simpa using (hp.comp_sub_left 0).symm
  have hneg : IntervalIntegrable (fun θ : ℝ => |θ| ^ (-a)) volume (-R) 0 := by
    apply hn.congr
    intro θ hθ
    rw [Set.uIoc_of_le (by linarith : -R ≤ 0)] at hθ
    simp only [abs_of_nonpos hθ.2]
  exact hneg.trans hpos

/-- Distance to the endpoints may carry an integrable power singularity at
both endpoints simultaneously. -/
theorem intervalIntegrable_endpoint_singular_power {b R : ℝ} (hb : b < 1) (hR : 0 < R) :
    IntervalIntegrable (fun θ : ℝ => (R - |θ|) ^ (-b)) volume (-R) R := by
  have hp := intervalIntegrable_singular_power hb R
  have hright : IntervalIntegrable (fun θ : ℝ => (R - θ) ^ (-b)) volume 0 R := by
    simpa using (hp.comp_sub_left R).symm
  have hpos : IntervalIntegrable (fun θ : ℝ => (R - |θ|) ^ (-b)) volume 0 R := by
    apply hright.congr
    intro θ hθ
    rw [Set.uIoc_of_le hR.le] at hθ
    simp only [abs_of_nonneg hθ.1.le]
  have hleft : IntervalIntegrable (fun θ : ℝ => (R + θ) ^ (-b)) volume (-R) 0 := by
    simpa using hp.comp_add_left R
  have hneg : IntervalIntegrable (fun θ : ℝ => (R - |θ|) ^ (-b)) volume (-R) 0 := by
    apply hleft.congr
    intro θ hθ
    rw [Set.uIoc_of_le (by linarith : -R ≤ 0)] at hθ
    simp only [abs_of_nonpos hθ.2, sub_neg_eq_add]
  exact hneg.trans hpos

/-- Closed-interval Lebesgue integrability of the central majorant. -/
theorem integrableOn_Icc_abs_singular_power {a R : ℝ} (ha : a < 1) (hR : 0 < R) :
    IntegrableOn (fun θ : ℝ => |θ| ^ (-a)) (Set.Icc (-R) R) volume :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -R ≤ R)).mp
    (intervalIntegrable_abs_singular_power ha hR)

/-- Closed-interval Lebesgue integrability of the endpoint majorant. -/
theorem integrableOn_Icc_endpoint_singular_power {b R : ℝ} (hb : b < 1) (hR : 0 < R) :
    IntegrableOn (fun θ : ℝ => (R - |θ|) ^ (-b)) (Set.Icc (-R) R) volume :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -R ≤ R)).mp
    (intervalIntegrable_endpoint_singular_power hb hR)

/-- The central angular singularity on the principal circle interval. -/
theorem intervalIntegrable_angular_singular_power {a : ℝ} (ha : a < 1) :
    IntervalIntegrable (fun θ : ℝ => |θ| ^ (-a)) volume (-Real.pi) Real.pi :=
  intervalIntegrable_abs_singular_power ha Real.pi_pos

/-- The singularity at the two representations of the opposite circle point. -/
theorem intervalIntegrable_angular_endpoint_power {b : ℝ} (hb : b < 1) :
    IntervalIntegrable (fun θ : ℝ => (Real.pi - |θ|) ^ (-b)) volume (-Real.pi) Real.pi :=
  intervalIntegrable_endpoint_singular_power hb Real.pi_pos

end ProofProject
