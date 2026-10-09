import NLA.TR07.UniformMean
import NLA.TR07.Asymptotics

/-! Complete original TR-07 theorem. The independent Challenge is not imported. -/
noncomputable section
open Filter
open scoped Topology
namespace NLA.TR07

/-- Random column subsets of every deterministic fixed-sparsity matrix family
have smallest singular value tending to zero in probability. -/
theorem random_column_subsets : SolvesTR07 := by
  intro s hs C hC r n hrk hrn hkr hnr M hM η hη
  have hC0 : 0 < C := by linarith
  have hβ : 0 < (2*C)⁻¹ := by positivity
  have hβ1 : (2*C)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ (by positivity : (0:ℝ) < 2*C)).mpr
    linarith
  obtain ⟨R,ρ,hρ,hmean⟩ := uniform_expected_defect s hs hβ hβ1 hη
  obtain ⟨hrpos, hrInf⟩ := aspect_ratio_bounds hC hkr
  have hbound : ∀ᶠ k in atTop,
      subsetTail (M k) (r k) η ≤ (4/ρ^2)*(r k:ℝ)⁻¹ + ρ⁻¹*((r k:ℝ)/(n k:ℝ)) := by
    filter_upwards [hM, hrpos, hrInf.eventually_ge_atTop R] with k hk hpos hR
    have hn : 0 < n k := hpos.1.trans_le (hrn k)
    exact subsetTail_le_simplified (M k) η hρ
      (subsetTail_le_of_defect_mean (M k) η hn hpos.1 (hrn k) hρ
        (hmean k (n k) (r k) hR (hrk k) hpos.2 hn (M k) hk))
  exact squeeze_zero' (Eventually.of_forall (fun k => subsetTail_nonneg (M k) (r k) η))
    hbound (probability_bound_tendsto_zero hrInf hnr ρ)

end NLA.TR07
