import OAI.Analysis.DirectCrouzeix.BoundaryKernel

namespace OAI

universe u_117 u_118 u_119 u_120 u_121 u_122 u_123 u_124 u_125 u_126 u_127 u_128

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem weighted_integral_norm_sq_le {α : Type u_117} {E : Type u_118} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) (k : α → ℝ) (u : α → E)
    (hk : ∀ x, 0 ≤ k x) (hki : Integrable k μ)
    (hui : Integrable (fun x => k x • u x) μ)
    (hsqi : Integrable (fun x => k x * ‖u x‖ ^ 2) μ)
    (hmass : ∫ x, k x ∂μ = 1) :
    ‖∫ x, k x • u x ∂μ‖ ^ 2 ≤ ∫ x, k x * ‖u x‖ ^ 2 ∂μ := by
  let v := ∫ x, k x • u x ∂μ
  have hii : Integrable (fun x => inner ℝ v (k x • u x)) μ :=
    (innerSL ℝ v).integrable_comp hui
  have hi : (∫ x, inner ℝ v (k x • u x) ∂μ) = ‖v‖ ^ 2 := by
    change (∫ x, (innerSL ℝ v) (k x • u x) ∂μ) = _
    rw [(innerSL ℝ v).integral_comp_comm hui]
    exact real_inner_self_eq_norm_sq v
  have hn : 0 ≤ ∫ x, k x * ‖u x - v‖ ^ 2 ∂μ :=
    integral_nonneg (fun x => mul_nonneg (hk x) (sq_nonneg _))
  have hexp : (fun x => k x * ‖u x - v‖ ^ 2) =
      fun x => (k x * ‖u x‖ ^ 2 - 2 * inner ℝ v (k x • u x)) + k x * ‖v‖ ^ 2 := by
    funext x
    rw [norm_sub_sq_real, inner_smul_right, real_inner_comm v (u x)]
    ring
  rw [hexp] at hn
  have hsubi : Integrable (fun x => k x * ‖u x‖ ^ 2 - 2 * inner ℝ v (k x • u x)) μ :=
    hsqi.sub (hii.const_mul 2)
  have hconsti : Integrable (fun x => k x * ‖v‖ ^ 2) μ := hki.mul_const _
  rw [integral_add hsubi hconsti, integral_sub hsqi (hii.const_mul 2),
    integral_const_mul, integral_mul_const, hi, hmass] at hn
  change ‖v‖ ^ 2 ≤ _
  linarith

theorem continuous_integrable_compact {α : Type u_119} {E : Type u_120} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [CompactSpace α]
    [NormedAddCommGroup E] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem continuous_integral_compact {α : Type u_121} {β : Type u_122} {E : Type u_123}
    [TopologicalSpace α] [FirstCountableTopology α] [LocallyCompactSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
    [CompactSpace β] [SecondCountableTopology β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure β) [IsFiniteMeasure μ] {f : α → β → E}
    (hf : Continuous f.uncurry) : Continuous (fun x => ∫ y, f x y ∂μ) := by
  simpa using continuous_parametric_integral_of_continuous (μ := μ) hf isCompact_univ

theorem markov_kernel_contraction {α : Type u_124} {β : Type u_125} {E : Type u_126}
    [MetricSpace α] [MeasurableSpace α] [BorelSpace α] [CompactSpace α]
    [SecondCountableTopology α]
    [MetricSpace β] [MeasurableSpace β] [BorelSpace β] [CompactSpace β]
    [SecondCountableTopology β]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (K : α → β → ℝ) (u : α → E)
    (hK : Continuous K.uncurry) (hu : Continuous u)
    (hpos : ∀ x y, 0 ≤ K x y)
    (hcol : ∀ y, ∫ x, K x y ∂μ = 1)
    (hrow : ∀ x, ∫ y, K x y ∂ν = 1) :
    (∫ y, ‖∫ x, K x y • u x ∂μ‖ ^ 2 ∂ν) ≤ ∫ x, ‖u x‖ ^ 2 ∂μ := by
  have hKcol (y : β) : Continuous (fun x => K x y) :=
    hK.comp (continuous_id.prodMk continuous_const)
  have hT : Continuous (fun y => ∫ x, K x y • u x ∂μ) := by
    apply continuous_integral_compact
    exact (hK.comp continuous_swap).smul (hu.comp continuous_snd)
  have hs : Integrable (fun p : α × β => K p.1 p.2 * ‖u p.1‖ ^ 2) (μ.prod ν) :=
    continuous_integrable_compact _ (hK.mul ((hu.comp continuous_fst).norm.pow 2))
  calc
    _ ≤ ∫ y, ∫ x, K x y * ‖u x‖ ^ 2 ∂μ ∂ν := by
      apply integral_mono (continuous_integrable_compact _ (hT.norm.pow 2))
        hs.integral_prod_right
      intro y
      exact weighted_integral_norm_sq_le μ (fun x => K x y) u (fun x => hpos x y)
        (continuous_integrable_compact _ (hKcol y))
        (continuous_integrable_compact _ ((hKcol y).smul hu))
        (continuous_integrable_compact _ ((hKcol y).mul (hu.norm.pow 2))) (hcol y)
    _ = ∫ x, ∫ y, K x y * ‖u x‖ ^ 2 ∂ν ∂μ := (integral_integral_swap hs).symm
    _ = _ := by simp_rw [integral_mul_const, hrow, one_mul]

section Hilbert

variable {E : Type u_127} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def positiveSeries {N : ℕ} (C : Fin N → E) (t : Angle) : E :=
  ∑ k : Fin N, fourier (k:ℤ) t • C k

theorem continuous_positiveSeries {E : Type u_127} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {N : ℕ} (C : Fin N → E) :
    Continuous (positiveSeries C) := by
  exact continuous_finsetSum _ (fun k _ => (fourier (k:ℤ)).continuous.smul continuous_const)

theorem fourierCoeff_finite_smul {N : ℕ} (f : Fin N → Angle → ℂ)
    (hf : ∀ k, Continuous (f k)) (C : Fin N → E) (j : ℤ) :
    fourierCoeff (fun t => ∑ k, f k t • C k) j = ∑ k, fourierCoeff (f k) j • C k := by
  unfold fourierCoeff
  simp_rw [Finset.smul_sum,smul_smul]
  rw [integral_finsetSum]
  · simp_rw [integral_smul_const,smul_eq_mul]
  · intro k hk
    exact integrable_of_continuous_compact _ (((fourier (-j)).continuous.mul (hf k)).smul continuous_const)

theorem fourierCoeff_positiveSeries {N : ℕ} (C : Fin N → E) (j : Fin N) :
    fourierCoeff (positiveSeries C) (j:ℤ) = C j := by
  classical
  unfold positiveSeries
  rw [fourierCoeff_finite_smul _ (fun k => (fourier (k:ℤ)).continuous)]
  simp_rw [fourierCoeff_fourier]
  simp only [Pi.single_apply,ite_smul,one_smul,zero_smul]
  have hinj (k : Fin N) : (j:ℤ) = (k:ℤ) ↔ j = k := by
    constructor
    · intro h; apply Fin.ext; exact_mod_cast h
    · intro h; rw [h]
  simp_rw [hinj]
  simp

theorem integral_inner_positiveSeries {N : ℕ} (C : Fin N → E)
    (f : Angle → E) (hf : Continuous f) :
    (∫ t, inner ℂ (positiveSeries C t) (f t) ∂angularMeasure) =
      ∑ k, inner ℂ (C k) (fourierCoeff f (k:ℤ)) := by
  simp only [positiveSeries,sum_inner,inner_smul_left,← fourier_neg]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    have he : (fun t => fourier (-(k:ℤ)) t * inner ℂ (C k) (f t)) =
        (fun t => inner ℂ (C k) (fourier (-(k:ℤ)) t • f t)) := by
      funext t; simp only [inner_smul_right]
    rw [he,integral_inner]
    · rfl
    · exact integrable_of_continuous_compact _ ((fourier (-(k:ℤ))).continuous.smul hf)
  · intro k hk
    exact integrable_of_continuous_compact _
      ((fourier (-(k:ℤ))).continuous.mul (continuous_const.inner hf))

theorem energy_positiveSeries {N : ℕ} (C : Fin N → E) :
    (∫ t, ‖positiveSeries C t‖^2 ∂angularMeasure) = ∑ k, ‖C k‖^2 := by
  have hp := continuous_positiveSeries C
  have he (t : Angle) : ‖positiveSeries C t‖^2 = RCLike.re (inner ℂ (positiveSeries C t) (positiveSeries C t)) := by
    simp [inner_self_eq_norm_sq_to_K,← Complex.ofReal_pow]
  simp_rw [he]
  rw [integral_re (integrable_of_continuous_compact _ (hp.inner hp)),integral_inner_positiveSeries C _ hp]
  simp only [fourierCoeff_positiveSeries,inner_self_eq_norm_sq_to_K,map_sum]
  change (∑ k, ((‖C k‖ : ℂ)^2).re) = ∑ k, ‖C k‖^2
  simp [← Complex.ofReal_pow]

theorem energy_orthogonal_positiveSeries {N : ℕ} (C : Fin N → E)
    (r : Angle → E) (hr : Continuous r) (hfreq : ∀ j : ℤ, 0 ≤ j → fourierCoeff r j = 0) :
    (∫ t, ‖positiveSeries C t+r t‖^2 ∂angularMeasure) =
      (∑ k, ‖C k‖^2) + ∫ t, ‖r t‖^2 ∂angularMeasure := by
  have hp := continuous_positiveSeries C
  have hci : Integrable (fun t => inner ℂ (positiveSeries C t) (r t)) angularMeasure :=
    integrable_of_continuous_compact _ (hp.inner hr)
  have hcross : (∫ t, inner ℂ (positiveSeries C t) (r t) ∂angularMeasure) = 0 := by
    rw [integral_inner_positiveSeries C r hr]
    apply Finset.sum_eq_zero
    intro k hk
    rw [hfreq (k:ℤ) (by positivity),inner_zero_right]
  have hcrossRe : (∫ t, RCLike.re (inner ℂ (positiveSeries C t) (r t)) ∂angularMeasure) = 0 := by
    rw [integral_re hci,hcross]
    rfl
  have hpi : Integrable (fun t => ‖positiveSeries C t‖^2) angularMeasure :=
    integrable_of_continuous_compact _ (hp.norm.pow 2)
  have hri : Integrable (fun t => ‖r t‖^2) angularMeasure := integrable_of_continuous_compact _ (hr.norm.pow 2)
  have hcii : Integrable (fun t => 2*RCLike.re (inner ℂ (positiveSeries C t) (r t))) angularMeasure :=
    hci.re.const_mul 2
  simp_rw [norm_add_sq (𝕜 := ℂ)]
  have ha := integral_add (hpi.add hcii) hri
  have hb := integral_add hpi hcii
  simp only [Pi.add_apply] at ha hb
  rw [ha,hb,integral_const_mul,hcrossRe,mul_zero,add_zero,energy_positiveSeries]

end Hilbert

section FaberHilbert

variable {E : Type u_128} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FaberHilbert

end DirectCrouzeix.Faber

end

end

end OAI
