import NLA.Proofs.TR06.NormalizedGraphChartsBasic
import NLA.Proofs.TR06.HomogeneousGaussianScaling
import NLA.TR06.Rectangular

/-! Finite actual normalized-graph volume bounds the actual annular input
volume through the literal 1-Lipschitz input projection. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.NormalizedGraphArea
open scoped ENNReal MeasureTheory
open MeasureTheory Set NLA.TR06 NormalizedGraphCharts
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

theorem inputProjection_lipschitz :
    LipschitzWith 1 (inputProjection (d := d) (n := n) (r := r)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,← map_sub]
  exact WithLp.norm_fst_le (Tensor ℝ d n) (x-y)

theorem annulus_subset_inputProjection_graph :
    HomogeneousGaussian.annulus (smoothRegularSet d n r) ⊆
      inputProjection '' normalizedAnnularGraph d n r := by
  intro A hA
  obtain ⟨c,u,hu,hcu⟩ := hA.1
  have hdec : Decomposes (c.summands u) A := by
    have h := c.decomposes u hu
    rwa [hcu] at h
  refine ⟨normalizedGraphPoint A (c.summands u),?_,rfl⟩
  refine ⟨hA.1,?_,?_,c.summands u,hdec,rfl⟩
  · exact lt_of_lt_of_le (by norm_num : (1/2 : ℝ) < 1) hA.2.1
  · exact hA.2.2.trans (by norm_num)

theorem annular_volume_le_graph_volume :
    (Measure.euclideanHausdorffMeasure (expectedDimension d n r))
      (HomogeneousGaussian.annulus (smoothRegularSet d n r)) ≤
      (Measure.euclideanHausdorffMeasure (expectedDimension d n r))
        (normalizedAnnularGraph d n r) := by
  calc
    _ ≤ (Measure.euclideanHausdorffMeasure (expectedDimension d n r))
        (inputProjection '' normalizedAnnularGraph d n r) :=
      measure_mono annulus_subset_inputProjection_graph
    _ ≤ _ := by
      have h := Area.euclidean_image_le_of_lipschitzOn (s := normalizedAnnularGraph d n r)
        (inputProjection_lipschitz (d := d) (n := n) (r := r)).lipschitzOnWith
        (expectedDimension d n r)
      simpa only [ENNReal.coe_one,one_pow,one_mul] using h

theorem annular_volume_lt_top_of_graph_volume_lt_top
    (hfinite : (Measure.euclideanHausdorffMeasure (expectedDimension d n r))
      (normalizedAnnularGraph d n r) < ⊤) :
    (Measure.euclideanHausdorffMeasure (expectedDimension d n r))
      (HomogeneousGaussian.annulus (smoothRegularSet d n r)) < ⊤ :=
  annular_volume_le_graph_volume.trans_lt hfinite

#assert_trust kernel inputProjection_lipschitz
#assert_trust kernel annulus_subset_inputProjection_graph
#assert_trust kernel annular_volume_le_graph_volume
#assert_trust kernel annular_volume_lt_top_of_graph_volume_lt_top
#print axioms annular_volume_le_graph_volume
end NLA.Proofs.TR06.NormalizedGraphArea
