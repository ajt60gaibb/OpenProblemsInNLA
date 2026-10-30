import NLA.Proofs.RE06.GaussianStream

/-! Finite-valued selection preserves a uniform independent failure bound,
without a factor equal to the number of candidates. Null-measurable repair
events are handled by actual almost-everywhere measurable representatives. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
namespace NLA.Proofs.RE06

variable {Ω β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
variable [Fintype β] [MeasurableSingletonClass β]

/-- Literal disjoint-fiber representation of a selected event. -/
theorem finite_selected_set_eq_union (K : Ω → β) (Y : Ω → γ) (E : β → Set γ) :
    {ω | Y ω ∈ E (K ω)} = ⋃ b, (K ⁻¹' {b}) ∩ (Y ⁻¹' E b) := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    exact ⟨K ω, rfl, h⟩
  · rintro ⟨b, hb, he⟩
    simpa only [hb] using he

/-- The finite partition cancels the apparent family-size factor. -/
theorem finite_selected_failure_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    (K : Ω → β) (hK : Measurable K) (Y : Ω → γ) (hKY : IndepFun K Y μ)
    (E : β → Set γ) (hE : ∀ b, MeasurableSet (E b)) (δ : ℝ)
    (hbound : ∀ b, μ.real (Y ⁻¹' E b) ≤ δ) :
    μ.real {ω | Y ω ∈ E (K ω)} ≤ δ := by
  have hpart : (∑ b, μ.real (K ⁻¹' {b})) = 1 := by
    simpa using sum_measureReal_preimage_singleton (μ := μ) (Finset.univ : Finset β)
      (fun b _ => hK (measurableSet_singleton b))
  have hi (b : β) : μ.real ((K ⁻¹' {b}) ∩ (Y ⁻¹' E b)) =
      μ.real (K ⁻¹' {b}) * μ.real (Y ⁻¹' E b) := by
    simp only [Measure.real,
      hKY.measure_inter_preimage_eq_mul {b} (E b) (measurableSet_singleton b) (hE b),
      ENNReal.toReal_mul]
  calc
    _ = μ.real (⋃ b, (K ⁻¹' {b}) ∩ (Y ⁻¹' E b)) := by rw [finite_selected_set_eq_union]
    _ ≤ ∑ b, μ.real ((K ⁻¹' {b}) ∩ (Y ⁻¹' E b)) := measureReal_iUnion_fintype_le _
    _ = ∑ b, μ.real (K ⁻¹' {b}) * μ.real (Y ⁻¹' E b) := by simp_rw [hi]
    _ ≤ ∑ b, μ.real (K ⁻¹' {b}) * δ := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (hbound b) measureReal_nonneg
    _ = δ := by rw [← Finset.sum_mul, hpart, one_mul]

/-- AE-measurable repair events suffice; their actual selected event remains
null-measurable and has the same uniform independent failure bound. -/
theorem finite_selected_failure_le_nullMeasurable {μ : Measure Ω} [IsProbabilityMeasure μ]
    (K : Ω → β) (hK : Measurable K) (Y : Ω → γ) (hY : AEMeasurable Y μ)
    (hKY : IndepFun K Y μ) (E : β → Set γ)
    (hE : ∀ b, NullMeasurableSet (E b) (μ.map Y)) (δ : ℝ)
    (hbound : ∀ b, μ.real (Y ⁻¹' E b) ≤ δ) :
    NullMeasurableSet {ω | Y ω ∈ E (K ω)} μ ∧ μ.real {ω | Y ω ∈ E (K ω)} ≤ δ := by
  let E' (b : β) : Set γ := toMeasurable (μ.map Y) (E b)
  have hAE (b : β) : (Y ⁻¹' E' b) =ᵐ[μ] (Y ⁻¹' E b) :=
    ae_of_ae_map hY (hE b).toMeasurable_ae_eq
  have hselected : {ω | Y ω ∈ E' (K ω)} =ᵐ[μ] {ω | Y ω ∈ E (K ω)} := by
    have hall : ∀ᵐ ω ∂μ, ∀ b, ω ∈ (Y ⁻¹' E' b) ↔ ω ∈ (Y ⁻¹' E b) :=
      ae_all_iff.mpr hAE
    filter_upwards [hall] with ω hω
    exact hω (K ω)
  have hmeas : NullMeasurableSet {ω | Y ω ∈ E' (K ω)} μ := by
    rw [finite_selected_set_eq_union]
    apply NullMeasurableSet.iUnion
    intro b
    exact (hK (measurableSet_singleton b)).nullMeasurableSet.inter
      (hY.nullMeasurableSet_preimage (measurableSet_toMeasurable _ _))
  constructor
  · exact hmeas.congr hselected
  · rw [← measureReal_congr hselected]
    apply finite_selected_failure_le K hK Y hKY E'
      (fun b => measurableSet_toMeasurable _ _) δ
    intro b
    rw [measureReal_congr (hAE b)]
    exact hbound b

#assert_trust kernel finite_selected_set_eq_union
#assert_trust kernel finite_selected_failure_le
#assert_trust kernel finite_selected_failure_le_nullMeasurable
#print axioms finite_selected_set_eq_union
#print axioms finite_selected_failure_le
#print axioms finite_selected_failure_le_nullMeasurable
end NLA.Proofs.RE06
