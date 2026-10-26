import NLA.Proofs.RE06.RepairMeasurable

/-! Markov assembly for a genuine nonnegative excess, including an exactly
zero spectral tail. The analytic expectation remains an internal premise. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory Filter
namespace NLA.Proofs.RE06.Repair

theorem nonnegative_majorant_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f Z : Ω → ℝ) (t η α : ℝ)
    (ht : 0 ≤ t) (hη : 0 < η) (hα : 0 ≤ α)
    (hZ : ∀ ω, 0 ≤ Z ω) (hZI : Integrable Z μ)
    (hmajorant : ∀ᵐ ω ∂μ, f ω ≤ t+Z ω)
    (hIntegral : (∫ ω, Z ω ∂μ) ≤ α*t) :
    μ.real {ω | (1+η)*t < f ω} ≤ α/η := by
  by_cases ht0 : t=0
  · have hInt0 : (∫ ω, Z ω ∂μ)=0 := by
      have hn := integral_nonneg_of_ae (ae_of_all μ hZ)
      rw [ht0, mul_zero] at hIntegral
      exact le_antisymm hIntegral hn
    have hZero : Z =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hZ) hZI).mp hInt0
    have he : {ω | (1+η)*t < f ω} =ᵐ[μ] (∅ : Set Ω) := by
      filter_upwards [hmajorant,hZero] with ω hm hz
      apply propext
      change ((1+η)*t<f ω) ↔ False
      simp only [ht0, mul_zero, Pi.zero_apply] at hm hz ⊢
      rw [hz] at hm
      exact iff_false_intro (not_lt_of_ge (by simpa only [zero_add] using hm))
    rw [measureReal_congr he, measureReal_empty]
    exact div_nonneg hα hη.le
  · have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hsub : {ω | (1+η)*t < f ω} ≤ᵐ[μ] {ω | η*t≤Z ω} := by
      filter_upwards [hmajorant] with ω hm
      intro hbad
      change η*t≤Z ω
      change (1+η)*t<f ω at hbad
      nlinarith
    have hp : μ.real {ω | (1+η)*t < f ω} ≤ μ.real {ω | η*t≤Z ω} := by
      exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
    have hMark := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hZ) hZI (η*t)
    have hMul : (η*t)*μ.real {ω | (1+η)*t < f ω} ≤ α*t :=
      (mul_le_mul_of_nonneg_left hp (mul_nonneg hη.le ht)).trans (hMark.trans hIntegral)
    have hCancel : μ.real {ω | (1+η)*t < f ω}*η ≤ α := by
      apply (mul_le_mul_iff_left₀ htpos).mp
      nlinarith [hMul]
    exact (le_div_iff₀ hη).mpr hCancel

#assert_trust kernel nonnegative_majorant_tail_bound
#print axioms nonnegative_majorant_tail_bound
end NLA.Proofs.RE06.Repair
