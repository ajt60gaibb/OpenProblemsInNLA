import ProofProject.FiniteMomentOrthogonality
import ProofProject.BasisEnergy

/-!
# The actual weighted monomials in a Hilbert space

Use ordinary angular `L²` and embed a polynomial as `ψ p / sqrt(D)`, where
`D=∫|ψ|²`. This gives exactly the source's normalized weighted polynomial norm;
using unnormalized angular measure cancels in the ratio.
-/

noncomputable section

open MeasureTheory

namespace ProofProject

abbrev SourceAngularL2 := Lp ℂ 2 (volume.restrict (Set.Icc (-Real.pi) Real.pi))

def sourceWeightMass (α : ℝ) : ℝ :=
  ∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi, ‖sourceWeightFactor α (sourceCircle θ)‖ ^ 2

lemma sourceWeightMass_nonneg (α : ℝ) : 0 ≤ sourceWeightMass α :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- Nonzero constant moment prevents the weight's integral from vanishing. -/
theorem sourceWeightMass_pos {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 < sourceWeightMass α := by
  apply lt_of_le_of_ne (sourceWeightMass_nonneg α)
  intro heq
  have hint : IntegrableOn (fun θ => ‖sourceWeightFactor α (sourceCircle θ)‖ ^ 2)
      (Set.Icc (-Real.pi) Real.pi) := by
    simpa only [Complex.ofReal_one, one_mul] using
      sourceWeightFactor_radial_norm_sq_integrable hα0 hα1 (r := 1) (by norm_num) (by norm_num)
  have hz := (integral_eq_zero_iff_of_nonneg (fun θ => sq_nonneg
    ‖sourceWeightFactor α (sourceCircle θ)‖) hint).mp heq.symm
  have hψ : (fun θ => sourceWeightFactor α (sourceCircle θ)) =ᵐ[
      volume.restrict (Set.Icc (-Real.pi) Real.pi)] 0 := by
    filter_upwards [hz] with θ hθ
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hθ)
  have hzero : (∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi,
      sourceWeightFactor α (sourceCircle θ)) = 0 := by
    rw [integral_congr_ae hψ]
    simp
  have hmom : (∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi,
      sourceWeightFactor α (sourceCircle θ)) = (2 * Real.pi : ℂ) := by
    simpa [sourceAngularMoment] using sourceAngularMoment_sourceWeightFactor hα0 hα1 0
  have hπ : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact hπ (hmom.symm.trans hzero)

/-- The norm identity for an actual complex `L²` representative. -/
theorem norm_sq_toLp_complex {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hf.toLp f))]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, inner_self_eq_norm_sq]

def sourceWeightedMonomial (α : ℝ) (j : ℕ) (θ : ℝ) : ℂ :=
  sourceWeightFactor α (sourceCircle θ) * sourceCircle θ ^ j

lemma norm_sourceWeightedMonomial (α θ : ℝ) (j : ℕ) :
    ‖sourceWeightedMonomial α j θ‖ = ‖sourceWeightFactor α (sourceCircle θ)‖ := by
  simp [sourceWeightedMonomial, norm_pow]

lemma sourceWeightedMonomial_memLp {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (j : ℕ) :
    MemLp (sourceWeightedMonomial α j) 2 (volume.restrict (Set.Icc (-Real.pi) Real.pi)) := by
  apply (memLp_two_iff_integrable_sq_norm
    (((measurable_sourceWeightFactor α).comp measurable_sourceCircle).mul
      (measurable_sourceCircle.pow_const j)).aestronglyMeasurable).mpr
  simpa only [IntegrableOn, Pi.mul_apply, Function.comp_apply, norm_mul, norm_pow,
    norm_sourceCircle, one_pow, mul_one, Complex.ofReal_one, one_mul] using
    sourceWeightFactor_radial_norm_sq_integrable hα0 hα1 (r := 1) (by norm_num) (by norm_num)

def sourceMonomialL2 (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (j : ℕ) : SourceAngularL2 :=
  (sourceWeightedMonomial_memLp hα0 hα1 j).toLp (sourceWeightedMonomial α j)

lemma sourceMonomialL2_norm_sq {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (j : ℕ) :
    ‖sourceMonomialL2 α hα0 hα1 j‖ ^ 2 = sourceWeightMass α := by
  rw [sourceMonomialL2, norm_sq_toLp_complex]
  simp only [norm_sourceWeightedMonomial, sourceWeightMass]

/-- The source's unit monomial family in an actual complex Hilbert space. -/
def sourceUnitFamily {n : ℕ} (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (i : Fin n) :
    SourceAngularL2 :=
  ((Real.sqrt (sourceWeightMass α))⁻¹ : ℂ) • sourceMonomialL2 α hα0 hα1 i.val

theorem sourceUnitFamily_norm {n : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (i : Fin n) :
    ‖sourceUnitFamily α hα0 hα1 i‖ = 1 := by
  have hmass := sourceWeightMass_pos hα0 hα1
  have hs := Real.sqrt_pos.mpr hmass
  have hn : ‖sourceMonomialL2 α hα0 hα1 i.val‖ = Real.sqrt (sourceWeightMass α) := by
    rw [← sourceMonomialL2_norm_sq hα0 hα1 i.val, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
  rw [sourceUnitFamily, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs, hn, inv_mul_cancel₀ hs.ne']

lemma sourceUnitFamily_coe {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (i : Fin n) :
    (sourceUnitFamily α hα0 hα1 i : ℝ → ℂ) =ᵐ[
        volume.restrict (Set.Icc (-Real.pi) Real.pi)]
      (fun θ => (Real.sqrt (sourceWeightMass α) : ℂ)⁻¹ *
        (sourceWeightFactor α (sourceCircle θ) * sourceCircle θ ^ i.val)) := by
  filter_upwards [Lp.coeFn_smul (Real.sqrt (sourceWeightMass α) : ℂ)⁻¹
    (sourceMonomialL2 α hα0 hα1 i.val),
    (sourceWeightedMonomial_memLp hα0 hα1 i.val).coeFn_toLp] with θ hs hm
  change (sourceUnitFamily α hα0 hα1 i) θ =
    (Real.sqrt (sourceWeightMass α) : ℂ)⁻¹ * (sourceMonomialL2 α hα0 hα1 i.val) θ at hs
  rw [hs]
  change (sourceMonomialL2 α hα0 hα1 i.val) θ = sourceWeightedMonomial α i.val θ at hm
  rw [hm]
  rfl

/-- Synthesis in the actual Hilbert family represents the source's normalized
weighted polynomial, as an equality of almost-everywhere classes. -/
theorem sourceUnitFamily_synthesis_ae {n : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (a : Fin n → ℂ) :
    ((finiteSynthesis (sourceUnitFamily α hα0 hα1) a : SourceAngularL2) : ℝ → ℂ) =ᵐ[
        volume.restrict (Set.Icc (-Real.pi) Real.pi)]
      (fun θ => (Real.sqrt (sourceWeightMass α) : ℂ)⁻¹ *
        (sourceWeightFactor α (sourceCircle θ) * sourcePolynomial a θ)) := by
  have ht : ∀ i, ((a i • sourceUnitFamily α hα0 hα1 i : SourceAngularL2) : ℝ → ℂ) =ᵐ[
      volume.restrict (Set.Icc (-Real.pi) Real.pi)]
      (fun θ => a i * ((Real.sqrt (sourceWeightMass α) : ℂ)⁻¹ *
        (sourceWeightFactor α (sourceCircle θ) * sourceCircle θ ^ i.val))) := by
    intro i
    filter_upwards [Lp.coeFn_smul (a i) (sourceUnitFamily α hα0 hα1 i),
      sourceUnitFamily_coe hα0 hα1 i] with θ hs hu
    change (a i • sourceUnitFamily α hα0 hα1 i) θ = a i * _ at hs
    rw [hs, hu]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i => a i • sourceUnitFamily α hα0 hα1 i), ae_all_iff.mpr ht] with θ hs ht
  change (∑ i, a i • sourceUnitFamily α hα0 hα1 i) θ = _
  rw [hs]
  simp_rw [ht]
  simp only [sourcePolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The Hilbert synthesis norm is exactly the normalized source energy. -/
theorem sourceUnitFamily_synthesis_norm_sq {n : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (a : Fin n → ℂ) :
    ‖finiteSynthesis (sourceUnitFamily α hα0 hα1) a‖ ^ 2 =
      (sourceWeightMass α)⁻¹ * (∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi,
        ‖sourceWeightFactor α (sourceCircle θ) * sourcePolynomial a θ‖ ^ 2) := by
  let v := finiteSynthesis (sourceUnitFamily α hα0 hα1) a
  have hv : ‖v‖ ^ 2 = ∫ θ, ‖v θ‖ ^ 2 ∂volume.restrict (Set.Icc (-Real.pi) Real.pi) := by
    simpa only [Lp.toLp_coeFn] using norm_sq_toLp_complex (Lp.memLp v)
  rw [hv, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [sourceUnitFamily_synthesis_ae hα0 hα1 a] with θ hθ
  change ‖(finiteSynthesis (sourceUnitFamily α hα0 hα1) a) θ‖ ^ 2 = _
  rw [hθ, norm_mul, mul_pow, norm_inv, inv_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (sourceWeightMass_nonneg α)]

end ProofProject
