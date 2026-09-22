import NLA.IE22.SupremumSemantics

/-!
Deterministic near-extremizers from the fully verified IE-21 finite-size event.
Original mathematical proof: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE22
open NLA.IE21

theorem spherical_realization_from_finite_bound (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (t ε δ : ℝ) (ht : 0 < t ∧ t < 1)
    (hε : 0 < ε ∧ ε ≤ (1 - θ) / 2) (hδ : 0 < δ ∧ δ < 1)
    (hfail : finiteFailure m n t ε δ < 1) :
    ∃ A : Mat m n, UnitRows A ∧
      |normalizedDeletion θ A - gaussianTrim θ| ≤
        trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ)) := by
  classical
  let : IsProbabilityMeasure (matrixLaw m n) := (product_row_semantics m n (by omega)).1
  by_contra! hall
  have hsub : {A : Mat m n | UnitRows A} ⊆
      {A | ¬(0 < operatorNorm A ∧ |normalizedOperator A - 1| ≤ t ∧
        |normalizedDeletion θ A - gaussianTrim θ| ≤
          trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ)) ∧
        |deletionRatio θ A - gaussianTrim θ| ≤ finiteRatioError θ m n t ε δ)} := by
    intro A hA hgood
    exact (not_lt_of_ge hgood.2.2.1) (hall A hA)
  have hmass : (matrixLaw m n).real {A | UnitRows A} = 1 := by
    rw [measureReal_def, show (matrixLaw m n) {A | UnitRows A} = 1 from
      (product_row_semantics m n (by omega)).2.2]
    simp
  have hle := (measureReal_mono hsub (measure_ne_top _ _)).trans
    (finite_size_bound θ hθ m n hm hn t ε δ ht hε hδ)
  rw [hmass] at hle
  exact (not_lt_of_ge hle) hfail

lemma trimming_error_le_ratio_error (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (t ε δ : ℝ) (ht : 0 ≤ t ∧ t < 1) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ)) ≤ finiteRatioError θ m n t ε δ := by
  have hgap : 0 < 1 - θ := sub_pos.mpr hθ.2
  have ht0 := ht.1
  have hL : 0 ≤ truncationScale θ := by unfold truncationScale; positivity
  have hE : 0 ≤ trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ)) := by
    unfold trimmingError
    positivity
  unfold finiteRatioError
  apply (le_div_iff₀ (by linarith : 0 < 1 - t)).2
  nlinarith

theorem high_aspect_near_extremizers (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∃ A : Mat (m j) (n j), UnitRows A ∧
      sharpConstant θ - ε < normalizedSingular θ A := by
  obtain ⟨hadm, hfail, herr⟩ := aspect_schedule θ hθ m n hm hn hnlim hQlim
  have hc := constant_semantics θ hθ
  filter_upwards [hadm, hfail.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    herr.eventually (gt_mem_nhds (sq_pos_of_pos hε))] with j hj hfj hej
  obtain ⟨A, hA, hclose⟩ := spherical_realization_from_finite_bound θ hθ (m j) (n j)
    (hm j) hj.1 _ _ _ ⟨hj.2.1, hj.2.2.1⟩ ⟨hj.2.1, hj.2.2.2⟩
    ⟨hj.2.1, hj.2.2.1⟩ hfj
  refine ⟨A, hA, ?_⟩
  have hns := normalizedSingular_nonneg_sq θ hθ (hn j) A
  have herrlt := (hclose.trans (trimming_error_le_ratio_error θ hθ (m j) (n j)
    _ _ _ ⟨hj.2.1.le, hj.2.2.1⟩ hj.2.1.le hj.2.1.le)).trans_lt hej
  rcases lt_or_ge (sharpConstant θ) ε with hce | hec
  · linarith [hns.1]
  · have hlow := (abs_lt.mp herrlt).1
    nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hec)]

end NLA.IE22
