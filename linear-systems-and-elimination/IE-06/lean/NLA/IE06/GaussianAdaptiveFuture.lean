import NLA.IE06.GaussianCoordinates

/-! Weighted transfer of an intrinsic event through exact selected-prefix and
fresh-column coordinates; part of the reviewed stage-smoothing contract. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
namespace NLA.IE06.GaussianAdaptiveFuture
open GaussianNull GaussianQuadratic GaussianPivotConditioning GaussianColumnSplit GaussianCoordinates

local instance gaussianMatrix_prob (d : ℕ) : IsProbabilityMeasure (gaussianMatrix d) :=
  gaussianMatrix_probability_proved d

theorem adaptive_lintegral_le {n t : ℕ} (ht : t ≤ n) (ε : ℝ≥0∞)
    (F : (π : Fin t ↪ Fin n) →
      (Mat t × (RemainingRows π → Fin t → ℝ)) × FutureBlock n t → ℝ≥0∞)
    (hF : ∀ π, Measurable (F π))
    (hbound : ∀ (π : Fin t ↪ Fin n) (T : Mat t), Good T →
      (∫⁻ Z, ∫⁻ W, F π ((T,Z),W) ∂futureLaw n t ∂Measure.pi
        (fun _ : RemainingRows π => GaussianRestriction.restrictedGaussian (truncationBody T))) ≤ ε) :
    (∑ π : Fin t ↪ Fin n, ∫⁻ A in orderEvent ht π,
      F π ((selectedBlock ht π A,remainingBlock ht π A),PivotFiltration.futureColumns t A)
        ∂gaussianMatrix n) ≤ ε := by
  by_cases hε : ε = ⊤
  · simp only [hε,le_top]
  have hsingle (π : Fin t ↪ Fin n) :
      (∫⁻ A in orderEvent ht π,
        F π ((selectedBlock ht π A,remainingBlock ht π A),PivotFiltration.futureColumns t A)
          ∂gaussianMatrix n) ≤ orderWeight π*ε := by
    rw [fixed_order_future_lintegral ht π (F π) (hF π)]
    calc
      _ ≤ ∫⁻ T in {T : Mat t | Good T},
          (gaussianVector t (truncationBody T))^(n-t)*ε ∂gaussianMatrix t :=
        setLIntegral_mono' (measurableSet_good t) (fun T hT =>
          mul_le_mul_of_nonneg_left (hbound π T hT) zero_le)
      _ = _ := lintegral_mul_const' ε _ hε
  calc
    _ ≤ ∑ π : Fin t ↪ Fin n, orderWeight π*ε := Finset.sum_le_sum (fun π _ => hsingle π)
    _ = (∑ π : Fin t ↪ Fin n, orderWeight π)*ε := (Finset.sum_mul _ _ _).symm
    _ = ε := by rw [orderWeights_sum_one ht,one_mul]

/-- Only the actual event is assumed measurable. Any auxiliary spectral frames
may be chosen separately on each fixed prefix fiber. -/
theorem event_le {n t : ℕ} (ht : t ≤ n) (B : Set (Mat n)) (hB : MeasurableSet B)
    (ε : ℝ≥0∞)
    (hbound : ∀ (π : Fin t ↪ Fin n) (T : Mat t), Good T →
      (∫⁻ Z, futureLaw n t {W | restore ht π ((T,Z),W) ∈ B} ∂Measure.pi
        (fun _ : RemainingRows π => GaussianRestriction.restrictedGaussian (truncationBody T))) ≤ ε) :
    gaussianMatrix n B ≤ ε := by
  classical
  let F (π : Fin t ↪ Fin n) := (restore ht π ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞))
  have hF (π : Fin t ↪ Fin n) : Measurable (F π) :=
    measurable_const.indicator (hB.preimage (restore_measurable ht π))
  have hfiber (π : Fin t ↪ Fin n) (T : Mat t) (Z : RemainingRows π → Fin t → ℝ) :
      (∫⁻ W, F π ((T,Z),W) ∂futureLaw n t) =
        futureLaw n t {W | restore ht π ((T,Z),W) ∈ B} := by
    change (∫⁻ W, {W | restore ht π ((T,Z),W) ∈ B}.indicator 1 W ∂_) = _
    apply lintegral_indicator_one
    exact hB.preimage ((restore_measurable ht π).comp (by fun_prop))
  have ha := adaptive_lintegral_le ht ε F hF (fun π T hT => by
    simp_rw [hfiber]
    exact hbound π T hT)
  have hone (π : Fin t ↪ Fin n) :
      (∫⁻ A in orderEvent ht π,
        F π ((selectedBlock ht π A,remainingBlock ht π A),PivotFiltration.futureColumns t A)
          ∂gaussianMatrix n) = gaussianMatrix n (orderEvent ht π ∩ B) := by
    have he (A : Mat n) :
        F π ((selectedBlock ht π A,remainingBlock ht π A),PivotFiltration.futureColumns t A) =
          B.indicator 1 A := by
      simp only [F,Set.indicator,Set.mem_preimage,restore_coordinates,Pi.one_apply]
    simp_rw [he]
    rw [lintegral_indicator_one hB,Measure.restrict_apply hB,Set.inter_comm]
  simp_rw [hone] at ha
  have hs : B = ⋃ π : Fin t ↪ Fin n, orderEvent ht π ∩ B := by
    ext A
    simp only [Set.mem_iUnion,Set.mem_inter_iff]
    exact ⟨fun hA => ⟨pivotOrder ht A,rfl,hA⟩,fun ⟨_,_,hA⟩ => hA⟩
  calc
    _ = gaussianMatrix n (⋃ π : Fin t ↪ Fin n, orderEvent ht π ∩ B) := congrArg _ hs
    _ ≤ ∑ π : Fin t ↪ Fin n, gaussianMatrix n (orderEvent ht π ∩ B) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ε := ha

#assert_trust kernel gaussianMatrix_prob
#assert_trust kernel adaptive_lintegral_le
#assert_trust kernel event_le
#print axioms adaptive_lintegral_le
#print axioms event_le
end NLA.IE06.GaussianAdaptiveFuture
