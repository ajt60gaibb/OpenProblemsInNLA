import ProofProject.SourcePolynomialInner
import ProofProject.SourcePhaseMeasure
import ProofProject.PhaseIntegralEnergy
import ProofProject.WeightedBoundaryEstimate
import ProofProject.TailBoundaryAlgebra

/-!
# The uniform boundary estimate for the actual source family

Raw angular integrals are used throughout. The mass `D` therefore equals
`2π d₀`, and the normalized Hilbert deficit is the raw deficit divided by `D`.
-/

noncomputable section

open MeasureTheory

namespace ProofProject

def sourceBoundaryConstant (M : ℝ) : ℝ :=
  1 + sourcePhaseQuotientIntegral (growthExponent M) *
    (6 * sourceWeightMass (growthExponent M) + (sourceWeightMass (growthExponent M))⁻¹)

theorem sourceBoundaryConstant_pos {M : ℝ} (hM : 1 < M) :
    0 < sourceBoundaryConstant M := by
  have hD := sourceWeightMass_pos (growthExponent_pos hM) (growthExponent_mem_Ioo hM).2
  have hJ := sourcePhaseQuotientIntegral_nonneg
    (growthExponent_pos hM) (growthExponent_mem_Ioo hM).2
  unfold sourceBoundaryConstant
  positivity

lemma sourceBoundaryPhase_mul_weighted (α θ : ℝ) (p : ℂ) :
    sourceBoundaryPhase α θ * (sourceWeightFactor α (sourceCircle θ) * p) =
      starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ)) * p := by
  unfold sourceBoundaryPhase
  by_cases h : sourceWeightFactor α (sourceCircle θ) = 0
  · simp [h]
  · field_simp

/-- The raw phase deficit is exactly the concrete Hilbert projection deficit
times the mass; conjugating the weight does not change either norm. -/
lemma source_phase_deficit_div_mass {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {n : ℕ} (M : ℝ) (a b : Fin n → ℂ) :
    phaseIntegralDeficit (volume.restrict (Set.Icc (-Real.pi) Real.pi)) M
      (fun θ => sourceWeightFactor α (sourceCircle θ) * sourcePolynomial a θ)
      (fun θ => starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ)) * sourcePolynomial b θ)
      (sourceBoundaryPhase α) / sourceWeightMass α =
      M ^ 2 * ‖finiteSynthesis (sourceUnitFamily α hα0 hα1) (a + b)‖ ^ 2 -
        ‖finiteSynthesis (sourceUnitFamily α hα0 hα1) a‖ ^ 2 := by
  rw [sourceUnitFamily_synthesis_norm_sq, sourceUnitFamily_synthesis_norm_sq]
  unfold phaseIntegralDeficit
  have heq : (fun θ => ‖sourceBoundaryPhase α θ *
      (sourceWeightFactor α (sourceCircle θ) * sourcePolynomial a θ) +
        starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ)) * sourcePolynomial b θ‖ ^ 2) =
      (fun θ => ‖sourceWeightFactor α (sourceCircle θ) * sourcePolynomial (a + b) θ‖ ^ 2) := by
    funext θ
    rw [sourceBoundaryPhase_mul_weighted, ← mul_add, sourcePolynomial_add,
      norm_mul, norm_mul, Complex.norm_conj]
  rw [heq]
  ring

/-- The boundary inequality for either split next to coefficient `i`. The
frequency cut supplies orthogonality, while its adjacency to `i` supplies
coefficient extraction. -/
theorem sourceUnitFamily_split_boundary {M : ℝ} (hM : 1 < M)
    {n cut : ℕ} (a b : Fin n → ℂ) (i : Fin n)
    (ha : ∀ j, a j ≠ 0 → cut ≤ j.val)
    (hb : ∀ j, b j ≠ 0 → j.val < cut)
    (hi : i.val ≤ cut) (hcut : cut ≤ i.val + 1) :
    ‖a i + b i‖ ^ 2 +
        ‖inner ℂ (sourceUnitFamily (growthExponent M) (growthExponent_pos hM)
          (growthExponent_mem_Ioo hM).2 i)
          (finiteSynthesis (sourceUnitFamily (growthExponent M) (growthExponent_pos hM)
            (growthExponent_mem_Ioo hM).2) a)‖ ^ 2 ≤
      sourceBoundaryConstant M *
        (M ^ 2 * ‖finiteSynthesis (sourceUnitFamily (growthExponent M) (growthExponent_pos hM)
          (growthExponent_mem_Ioo hM).2) (a + b)‖ ^ 2 -
          ‖finiteSynthesis (sourceUnitFamily (growthExponent M) (growthExponent_pos hM)
            (growthExponent_mem_Ioo hM).2) a‖ ^ 2) := by
  let α := growthExponent M
  have hα0 : 0 < α := growthExponent_pos hM
  have hα1 : α < 1 := (growthExponent_mem_Ioo hM).2
  let μ := volume.restrict (Set.Icc (-Real.pi) Real.pi)
  let ψ : ℝ → ℂ := fun θ => sourceWeightFactor α (sourceCircle θ)
  let A : ℝ → ℂ := fun θ => ψ θ * sourcePolynomial a θ
  let C : ℝ → ℂ := fun θ => starRingEnd ℂ (ψ θ) * sourcePolynomial b θ
  let g := sourceBoundaryPhase α
  let δ := sourcePhaseMargin α
  let E := phaseIntegralDeficit μ M A C g
  let D := sourceWeightMass α
  let J := sourcePhaseQuotientIntegral α
  let χ : ℝ → ℂ := fun θ => starRingEnd ℂ (sourceCircle θ ^ i.val)
  let F : ℝ → ℂ := fun θ => (A θ + C θ) * χ θ
  let G : ℝ → ℂ := fun θ => A θ * χ θ
  have hδ := measurable_sourcePhaseMargin α
  have hδpos := sourcePhaseMargin_ae_pos hα0 hα1
  have hψ : Measurable ψ := (measurable_sourceWeightFactor α).comp measurable_sourceCircle
  have hA : Measurable A := measurable_sourceWeightFactor_polynomial α a
  have hC : Measurable C := measurable_sourceConjWeightFactor_polynomial α b
  have hχ : Measurable χ := Complex.continuous_conj.measurable.comp
    (measurable_sourceCircle.pow_const i.val)
  have hχnorm (θ : ℝ) : ‖χ θ‖ = 1 := by simp [χ, norm_pow]
  have hF : Measurable F := (hA.add hC).mul hχ
  have hG : Measurable G := hA.mul hχ
  have horth : (∫ θ, star (A θ) * C θ ∂μ) = 0 :=
    sourceWeightFactor_polynomial_inner_integral_eq_zero hα0 hα1 a b ha hb
  have hmargin : ∀ᵐ θ ∂μ, δ θ = 2 * M⁻¹ * ((g θ).re - M⁻¹) :=
    Filter.Eventually.of_forall fun θ => sourcePhaseMargin_growthExponent_inv M θ hM.le
  obtain ⟨hE, hAi, hACi, hAbound, hACbound⟩ := phase_integral_energy_coarse hM
    (sourceWeightFactor_polynomial_memLp hα0 hα1 a)
    (sourceConjWeightFactor_polynomial_memLp hα0 hα1 b)
    (measurable_sourceBoundaryPhase α) (sourceBoundaryPhase_ae_norm α)
    hδ hmargin (hδpos.mono fun _ hx => hx.le) horth
  have hFnorm : (fun θ => δ θ * ‖F θ‖ ^ 2) =
      (fun θ => δ θ * ‖A θ + C θ‖ ^ 2) := by
    funext θ
    simp only [F, norm_mul, hχnorm, mul_one]
  have hGnorm : (fun θ => δ θ * ‖G θ‖ ^ 2) =
      (fun θ => δ θ * ‖A θ‖ ^ 2) := by
    funext θ
    simp only [G, norm_mul, hχnorm, mul_one]
  have hFE : Integrable (fun θ => δ θ * ‖F θ‖ ^ 2) μ := by
    rw [hFnorm]
    exact hACi
  have hGE : Integrable (fun θ => δ θ * ‖G θ‖ ^ 2) μ := by
    rw [hGnorm]
    exact hAi
  have hFb : (∫ θ, δ θ * ‖F θ‖ ^ 2 ∂μ) ≤ 6 * E := by rw [hFnorm]; exact hACbound
  have hGb : (∫ θ, δ θ * ‖G θ‖ ^ 2 ∂μ) ≤ E := by rw [hGnorm]; exact hAbound
  have ht : (∫ θ, F θ ∂μ) = (2 * Real.pi : ℂ) * (a i + b i) := by
    apply sourceWeightFactor_shifted_coefficient_integral hα0 hα1 a b i
    · intro j hj
      exact hi.trans (ha j hj)
    · intro j hj
      have := hb j hj
      omega
  have hbinner : (∫ θ, G θ * star (ψ θ) ∂μ) = (D : ℂ) *
      inner ℂ (sourceUnitFamily α hα0 hα1 i)
        (finiteSynthesis (sourceUnitFamily α hα0 hα1) a) := by
    rw [sourceUnitFamily_inner_synthesis, ← mul_assoc,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (sourceWeightMass_pos hα0 hα1).ne'), one_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun θ => by dsimp [G, A, χ, ψ]; ring
  have hbound := weighted_boundary_estimate μ hδ hδpos hF hG hψ hFE hGE
    (sourcePhaseMargin_inv_integrable hα0 hα1)
    (sourcePhaseMargin_weighted_inv_integrable hα0 hα1)
    (integral_inv_sourcePhaseMargin_le hα0 hα1)
    (integral_weighted_inv_sourcePhaseMargin_le hα0 hα1)
    (sourceWeightMass_pos hα0 hα1) (sourcePhaseQuotientIntegral_nonneg hα0 hα1)
    hE hFb hGb ht hbinner
  change _ ≤ sourceBoundaryConstant M * (E / D) at hbound
  rw [source_phase_deficit_div_mass hα0 hα1 M a b] at hbound
  exact hbound

/-- The actual source family has the uniform boundary estimate needed by
coefficient replication. The constant is chosen before the dimension. -/
theorem sourceUnitFamily_hasBoundaryEstimate {M : ℝ} (hM : 1 < M) (n : ℕ) :
    HasBoundaryEstimate
      (sourceUnitFamily (growthExponent M) (growthExponent_pos hM)
        (growthExponent_mem_Ioo hM).2 : Fin n → SourceAngularL2) M
      (sourceBoundaryConstant M) := by
  apply hasBoundaryEstimate_of_adjacent_tails
  intro c i k hik hki
  let a := sourceTailCoefficients c k
  let b := sourceHeadCoefficients c k
  have h := sourceUnitFamily_split_boundary hM a b i
    (sourceTailCoefficients_support c) (sourceHeadCoefficients_support c) hik hki
  have hab : a + b = c := sourceTailCoefficients_add_head c k
  change ‖(a + b) i‖ ^ 2 + _ ≤ _ at h
  rw [hab, finiteSynthesis_tailCoefficients] at h
  exact h

end ProofProject
