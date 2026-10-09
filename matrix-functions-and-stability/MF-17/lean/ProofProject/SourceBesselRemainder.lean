import ProofProject.BesselAsymptotic
import ProofProject.GammaKernelSeries
import ProofProject.SourcePieceLimit
import ProofProject.PowerTailIntegral

/-!
# A fixed integrable remainder for the actual Bessel kernel

The source cutoff removes the apparent singularity of the oscillatory model
at zero. Beyond the fixed cutoff, the checked Bessel asymptotic gives an
integrable `u^(-5/4)` remainder. Exponential damping only decreases its norm.
-/

noncomputable section

open MeasureTheory Set

namespace ProofProject

/-- Damping of a fixed scalar remainder. -/
def dampedRemainder (h : ℝ → ℂ) (t u : ℝ) : ℂ :=
  (Real.exp (-u / t) : ℂ) * h u

theorem dampedRemainder_of_nonpos {h : ℝ → ℂ}
    (hz : ∀ u, u ≤ 0 → h u = 0) (t : ℝ) {u : ℝ} (hu : u ≤ 0) :
    dampedRemainder h t u = 0 := by
  simp only [dampedRemainder, hz u hu, mul_zero]

theorem norm_dampedRemainder_le {h : ℝ → ℂ}
    (hz : ∀ u, u ≤ 0 → h u = 0) {t : ℝ} (ht : 0 < t) (u : ℝ) :
    ‖dampedRemainder h t u‖ ≤ ‖h u‖ := by
  by_cases hu : 0 ≤ u
  · rw [dampedRemainder, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    apply mul_le_of_le_one_left (norm_nonneg _)
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) ht.le)
  · simp only [dampedRemainder_of_nonpos hz t (le_of_not_ge hu),
      hz u (le_of_not_ge hu), norm_zero, le_refl]

theorem dampedRemainder_integrable {h : ℝ → ℂ} (hi : Integrable h)
    (hz : ∀ u, u ≤ 0 → h u = 0) {t : ℝ} (ht : 0 < t) :
    Integrable (dampedRemainder h t) := by
  have hc : Continuous (fun u : ℝ => (Real.exp (-u / t) : ℂ)) := by fun_prop
  exact hi.norm.mono' (hc.aestronglyMeasurable.mul hi.aestronglyMeasurable)
    (Filter.Eventually.of_forall (norm_dampedRemainder_le hz ht))

theorem integral_norm_dampedRemainder_le {h : ℝ → ℂ} (hi : Integrable h)
    (hz : ∀ u, u ≤ 0 → h u = 0) {t : ℝ} (ht : 0 < t) :
    (∫ u : ℝ, ‖dampedRemainder h t u‖) ≤ ∫ u : ℝ, ‖h u‖ :=
  integral_mono (dampedRemainder_integrable hi hz ht).norm hi.norm
    (norm_dampedRemainder_le hz ht)

private def besselOscillatoryModel (cPlus cMinus : ℂ) (u : ℝ) : ℂ :=
  cPlus * Complex.exp (((2 * Real.sqrt u : ℝ) : ℂ) * Complex.I) +
    cMinus * Complex.exp (((-(2 * Real.sqrt u) : ℝ) : ℂ) * Complex.I)

/-- Clipping at 32 makes continuity transparent; the cutoff makes this
identical to the original unmodified power at every argument. -/
private def besselCutoffModel (cPlus cMinus : ℂ) (u : ℝ) : ℂ :=
  ((1 - sourcePieceChi (u / 32) : ℝ) : ℂ) *
    (((max u 32) ^ (-3 / 4 : ℝ) : ℝ) : ℂ) * besselOscillatoryModel cPlus cMinus u

private theorem besselCutoffModel_eq (cPlus cMinus : ℂ) (u : ℝ) :
    besselCutoffModel cPlus cMinus u =
      ((1 - sourcePieceChi (u / 32) : ℝ) : ℂ) *
        ((u ^ (-3 / 4 : ℝ) : ℝ) : ℂ) * besselOscillatoryModel cPlus cMinus u := by
  by_cases hu : 32 ≤ u
  · simp only [besselCutoffModel, max_eq_left hu]
  · have hc : sourcePieceChi (u / 32) = 1 :=
      sourcePieceChi_eq_one ((div_le_one (by norm_num : (0 : ℝ) < 32)).mpr
        (le_of_not_ge hu))
    simp only [besselCutoffModel, hc, sub_self, Complex.ofReal_zero, zero_mul]

private theorem besselCutoffModel_continuous (cPlus cMinus : ℂ) :
    Continuous (besselCutoffModel cPlus cMinus) := by
  have hchi := sourcePieceChi_contDiff.continuous
  have hp : Continuous (fun u : ℝ => (max u 32) ^ (-3 / 4 : ℝ)) :=
    (continuous_id.max continuous_const).rpow_const (fun u => Or.inl
      (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) (le_max_right u 32))))
  have ho : Continuous (besselOscillatoryModel cPlus cMinus) := by
    unfold besselOscillatoryModel
    fun_prop
  exact ((Complex.continuous_ofReal.comp
    (continuous_const.sub (hchi.comp (continuous_id.div_const 32)))).mul
    (Complex.continuous_ofReal.comp hp)).mul ho

def sourceBesselRemainder (cPlus cMinus : ℂ) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator
    (fun u => (besselKernel u : ℂ) - besselCutoffModel cPlus cMinus u)

theorem sourceBesselRemainder_of_nonpos (cPlus cMinus : ℂ) {u : ℝ} (hu : u ≤ 0) :
    sourceBesselRemainder cPlus cMinus u = 0 :=
  indicator_of_notMem (not_lt_of_ge hu) _

private theorem sourceBesselRemainder_integrable {cPlus cMinus : ℂ} {C : ℝ}
    (hasymp : ∀ u : ℝ, 1 ≤ u →
      ‖(besselKernel u : ℂ) - ((u ^ (-3 / 4 : ℝ) : ℝ) : ℂ) *
        besselOscillatoryModel cPlus cMinus u‖ ≤ C * u ^ (-5 / 4 : ℝ)) :
    Integrable (sourceBesselRemainder cPlus cMinus) := by
  let R : ℝ → ℂ := fun u => (besselKernel u : ℂ) - besselCutoffModel cPlus cMinus u
  have hR : Continuous R :=
    (Complex.continuous_ofReal.comp besselKernel_continuous).sub
      (besselCutoffModel_continuous cPlus cMinus)
  have hsmall : IntegrableOn R (Ioc (0 : ℝ) 64) :=
    hR.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hlarge : IntegrableOn R (Ioi (64 : ℝ)) := by
    apply ((integrableOn_rpow_neg_five_quarters (by norm_num : (0 : ℝ) < 64)).const_mul C).mono'
      hR.aestronglyMeasurable.restrict
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro u hu
    change 64 < u at hu
    have hchi : sourcePieceChi (u / 32) = 0 :=
      sourcePieceChi_eq_zero ((le_div_iff₀ (by norm_num : (0 : ℝ) < 32)).mpr
        (by linarith : 2 * 32 ≤ u))
    simpa only [R, besselCutoffModel_eq, hchi, sub_zero, Complex.ofReal_one, one_mul]
      using hasymp u (by linarith)
  have hfull : IntegrableOn R (Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 64)]
    exact integrableOn_union.mpr ⟨hsmall, hlarge⟩
  exact (integrable_indicator_iff measurableSet_Ioi).mpr hfull

private theorem besselDampedKernel_decomposition (cPlus cMinus : ℂ) (t u : ℝ) :
    besselDampedKernel t u =
      cPlus * sourceOscillatoryTailKernel t 1 u +
      cMinus * sourceOscillatoryTailKernel t (-1) u +
      dampedRemainder (sourceBesselRemainder cPlus cMinus) t u := by
  by_cases hu : 0 < u
  · rw [besselDampedKernel_of_pos t hu, dampedRemainder, sourceBesselRemainder,
      indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu), besselCutoffModel_eq]
    simp only [sourceOscillatoryTailKernel, dampedPower, besselOscillatoryModel,
      one_mul, neg_mul]
    push_cast
    ring
  · have hu0 := le_of_not_gt hu
    rw [besselDampedKernel_of_nonpos t hu0,
      sourceOscillatoryTailKernel_eq_zero_of_le t 1 (by linarith : u ≤ 32),
      sourceOscillatoryTailKernel_eq_zero_of_le t (-1) (by linarith : u ≤ 32),
      dampedRemainder_of_nonpos (fun v hv => sourceBesselRemainder_of_nonpos cPlus cMinus hv) t hu0]
    simp only [mul_zero, add_zero]

/-- The constants and one integrable remainder are fixed before every damping
time. All analytic premises are supplied by the actual Bessel asymptotic. -/
theorem exists_bessel_tail_decomposition :
    ∃ cPlus cMinus : ℂ, ∃ h : ℝ → ℂ,
      Integrable h ∧ (∀ u, u ≤ 0 → h u = 0) ∧
      ∀ t : ℝ, 0 < t → ∀ u : ℝ,
        besselDampedKernel t u = cPlus * sourceOscillatoryTailKernel t 1 u +
          cMinus * sourceOscillatoryTailKernel t (-1) u + dampedRemainder h t u := by
  obtain ⟨cPlus, cMinus, C, _hC, hasymp⟩ := exists_besselKernel_asymptotic
  refine ⟨cPlus, cMinus, sourceBesselRemainder cPlus cMinus,
    sourceBesselRemainder_integrable hasymp, ?_, ?_⟩
  · exact fun u hu => sourceBesselRemainder_of_nonpos cPlus cMinus hu
  · exact fun t _ht u => besselDampedKernel_decomposition cPlus cMinus t u

end ProofProject
