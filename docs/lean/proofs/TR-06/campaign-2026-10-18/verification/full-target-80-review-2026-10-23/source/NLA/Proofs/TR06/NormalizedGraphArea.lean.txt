import NLA.Proofs.TR06.NormalizedGraphAreaPiece

/-! Actual annular angular integrability follows from finite volume of the
literal normalized decomposition graph. No annular integrability assumption is
used: a countable input partition selects disjoint actual graph branches. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.NormalizedGraphArea
open scoped ENNReal MeasureTheory
open MeasureTheory Set Function NLA.TR06 NormalizedGraphCharts
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

theorem annular_angularIntegral_le_graphVolume (hd : 0 < d) :
    (∫⁻ A in HomogeneousGaussian.annulus (smoothRegularSet d n r), angularSlope r A
      ∂(Measure.euclideanHausdorffMeasure (expectedDimension d n r))) ≤
      (Measure.euclideanHausdorffMeasure (expectedDimension d n r))
        (normalizedAnnularGraph d n r) := by
  classical
  by_cases hne : (HomogeneousGaussian.annulus (smoothRegularSet d n r)).Nonempty
  · obtain ⟨C,P,hPmeas,hPdisj,hcover,hPsub⟩ := exists_countable_input_partition hd hne
    let Q : ℕ → Set (NormalizedGraphAmbient d n r) := fun j => (C j).graphPiece (P j)
    have hQmeas : ∀ j, MeasurableSet (Q j) := fun j =>
      (C j).graphPiece_measurable (P j) (hPmeas j)
    have hQdisj : Pairwise (Disjoint on Q) := by
      intro i j hij
      apply disjoint_left.mpr
      intro z hi hj
      exact disjoint_left.mp (hPdisj hij)
        ((C i).inputProjection_mem_piece (P i) z hi)
        ((C j).inputProjection_mem_piece (P j) z hj)
    have hQsub : (⋃ j, Q j) ⊆ normalizedAnnularGraph d n r := by
      intro z hz
      obtain ⟨j,hj⟩ := mem_iUnion.mp hz
      exact (C j).graphPiece_subset (P j) hj
    calc
      _ = ∑' j, ∫⁻ A in P j, angularSlope r A
          ∂(Measure.euclideanHausdorffMeasure (expectedDimension d n r)) := by
        rw [hcover,lintegral_iUnion hPmeas hPdisj]
      _ ≤ ∑' j, (Measure.euclideanHausdorffMeasure (expectedDimension d n r)) (Q j) :=
        ENNReal.tsum_le_tsum (fun j =>
          (C j).piece_angularIntegral_le_graphVolume (P j) (hPmeas j) (hPsub j))
      _ = (Measure.euclideanHausdorffMeasure (expectedDimension d n r)) (⋃ j, Q j) :=
        (measure_iUnion hQdisj hQmeas).symm
      _ ≤ _ := measure_mono hQsub
  · rw [not_nonempty_iff_eq_empty.mp hne]
    simp

theorem actualAnnularBounds_of_graphVolume_lt_top (hd : 0 < d)
    (hfinite : (Measure.euclideanHausdorffMeasure (expectedDimension d n r))
      (normalizedAnnularGraph d n r) < ⊤) :
    (Measure.euclideanHausdorffMeasure (expectedDimension d n r))
        (HomogeneousGaussian.annulus (smoothRegularSet d n r)) < ⊤ ∧
      (∫⁻ A in HomogeneousGaussian.annulus (smoothRegularSet d n r), angularSlope r A
        ∂(Measure.euclideanHausdorffMeasure (expectedDimension d n r))) < ⊤ :=
  ⟨annular_volume_lt_top_of_graph_volume_lt_top hfinite,
    (annular_angularIntegral_le_graphVolume hd).trans_lt hfinite⟩

#assert_trust kernel annular_angularIntegral_le_graphVolume
#assert_trust kernel actualAnnularBounds_of_graphVolume_lt_top
#print axioms annular_angularIntegral_le_graphVolume
#print axioms actualAnnularBounds_of_graphVolume_lt_top
end NLA.Proofs.TR06.NormalizedGraphArea
