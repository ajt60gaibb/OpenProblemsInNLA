import ProofProject.AngularPowerIntegrals

/-!
# Integrability of a weight divided by its phase margin

A positive lower bound for the margin in terms of distance to the exceptional
angles gives an integrable majorant of order `α+ν<1`. The three exceptional
angles are removed only in the almost-everywhere comparison; the quotient
remains an ordinary measurable real function everywhere.
-/

noncomputable section

open MeasureTheory

namespace ProofProject

/-- Pointwise domination by the sum of the central and endpoint singularities.
Only interior, nonzero angles enter this scalar estimate. -/
theorem phase_quotient_norm_le {α ν K c θ w d : ℝ}
    (hα0 : 0 < α) (hK : 0 ≤ K) (hc : 0 < c)
    (hθ0 : 0 < |θ|) (hθπ : |θ| < Real.pi) (hw0 : 0 ≤ w)
    (hw : w ≤ K * |θ| ^ (-α))
    (hd : c * min |θ| (Real.pi - |θ|) ^ ν ≤ d) :
    ‖(1 + w) / d‖ ≤ ((Real.pi ^ α + K) / c) *
      (|θ| ^ (-(α + ν)) + (Real.pi - |θ|) ^ (-(α + ν))) := by
  let m := min |θ| (Real.pi - |θ|)
  have hm : 0 < m := lt_min hθ0 (sub_pos.mpr hθπ)
  have hmθ : m ≤ |θ| := min_le_left _ _
  have hmπ : m ≤ Real.pi := hmθ.trans hθπ.le
  have hp : 0 < m ^ α := Real.rpow_pos_of_pos hm _
  have hν : 0 < m ^ ν := Real.rpow_pos_of_pos hm _
  have hden : 0 < c * m ^ ν := mul_pos hc hν
  have hdpos : 0 < d := hden.trans_le hd
  have hw' : w ≤ K * m ^ (-α) := hw.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hm hmθ (by linarith)) hK)
  have hone : 1 ≤ Real.pi ^ α * m ^ (-α) := by
    rw [Real.rpow_neg hm.le]
    change 1 ≤ Real.pi ^ α / m ^ α
    exact (one_le_div hp).mpr (Real.rpow_le_rpow hm.le hmπ hα0.le)
  have hnum : 1 + w ≤ (Real.pi ^ α + K) * m ^ (-α) := by nlinarith
  have hcoef : 0 ≤ (Real.pi ^ α + K) / c := by positivity
  have hminpower : m ^ (-(α + ν)) ≤
      |θ| ^ (-(α + ν)) + (Real.pi - |θ|) ^ (-(α + ν)) := by
    by_cases h : |θ| ≤ Real.pi - |θ|
    · rw [show m = |θ| from min_eq_left h]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (sub_pos.mpr hθπ).le _)
    · rw [show m = Real.pi - |θ| from min_eq_right (le_of_not_ge h)]
      exact le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) hdpos.le)]
  calc
    _ ≤ ((Real.pi ^ α + K) * m ^ (-α)) / d :=
      div_le_div_of_nonneg_right hnum hdpos.le
    _ ≤ ((Real.pi ^ α + K) * m ^ (-α)) / (c * m ^ ν) :=
      div_le_div_of_nonneg_left (by positivity) hden hd
    _ = ((Real.pi ^ α + K) / c) * (m ^ (-α) / m ^ ν) := by ring
    _ = ((Real.pi ^ α + K) / c) * m ^ (-α - ν) := by rw [← Real.rpow_sub hm]
    _ = ((Real.pi ^ α + K) / c) * m ^ (-(α + ν)) := by congr 2; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hminpower hcoef

/-- An integrable pointwise majorant for the phase quotient on the principal
angular interval. Positive `ν` is allowed but is not needed beyond `α+ν<1`. -/
theorem integrableOn_phase_quotient {α ν K c : ℝ} {w d : ℝ → ℝ}
    (hα0 : 0 < α) (hαν : α + ν < 1) (hK : 0 ≤ K) (hc : 0 < c)
    (hw : Measurable w) (hd : Measurable d)
    (hw0 : ∀ θ, 0 < |θ| → |θ| < Real.pi → 0 ≤ w θ)
    (hwupper : ∀ θ, 0 < |θ| → |θ| < Real.pi → w θ ≤ K * |θ| ^ (-α))
    (hdlower : ∀ θ, 0 < |θ| → |θ| < Real.pi →
      c * min |θ| (Real.pi - |θ|) ^ ν ≤ d θ) :
    IntegrableOn (fun θ => (1 + w θ) / d θ) (Set.Icc (-Real.pi) Real.pi) volume := by
  have hmajor : IntegrableOn (fun θ : ℝ => ((Real.pi ^ α + K) / c) *
      (|θ| ^ (-(α + ν)) + (Real.pi - |θ|) ^ (-(α + ν))))
      (Set.Icc (-Real.pi) Real.pi) volume :=
    ((integrableOn_Icc_abs_singular_power hαν Real.pi_pos).add
      (integrableOn_Icc_endpoint_singular_power hαν Real.pi_pos)).const_mul _
  apply hmajor.mono' ((measurable_const.add hw).div hd).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    (volume.restrict (Set.Icc (-Real.pi) Real.pi)).ae_ne 0,
    (volume.restrict (Set.Icc (-Real.pi) Real.pi)).ae_ne Real.pi,
    (volume.restrict (Set.Icc (-Real.pi) Real.pi)).ae_ne (-Real.pi)] with θ hθ hθ0 hθπ hθnegπ
  have habspos : 0 < |θ| := abs_pos.mpr hθ0
  have habslt : |θ| < Real.pi := abs_lt.mpr
    ⟨lt_of_le_of_ne hθ.1 hθnegπ.symm, lt_of_le_of_ne hθ.2 hθπ⟩
  exact phase_quotient_norm_le hα0 hK hc habspos habslt
    (hw0 θ habspos habslt) (hwupper θ habspos habslt) (hdlower θ habspos habslt)

/-- The same quotient is interval integrable, for use in angular integral
identities and dominated convergence. -/
theorem intervalIntegrable_phase_quotient {α ν K c : ℝ} {w d : ℝ → ℝ}
    (hα0 : 0 < α) (hαν : α + ν < 1) (hK : 0 ≤ K) (hc : 0 < c)
    (hw : Measurable w) (hd : Measurable d)
    (hw0 : ∀ θ, 0 < |θ| → |θ| < Real.pi → 0 ≤ w θ)
    (hwupper : ∀ θ, 0 < |θ| → |θ| < Real.pi → w θ ≤ K * |θ| ^ (-α))
    (hdlower : ∀ θ, 0 < |θ| → |θ| < Real.pi →
      c * min |θ| (Real.pi - |θ|) ^ ν ≤ d θ) :
    IntervalIntegrable (fun θ => (1 + w θ) / d θ) volume (-Real.pi) Real.pi :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])).mpr
    (integrableOn_phase_quotient hα0 hαν hK hc hw hd hw0 hwupper hdlower)

end ProofProject
