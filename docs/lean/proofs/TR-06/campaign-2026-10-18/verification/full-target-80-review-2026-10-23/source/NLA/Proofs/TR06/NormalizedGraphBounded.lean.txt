import NLA.Proofs.TR06.NormalizedGraphEuclidean

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR06
open Set NLA.TR06 NLA.TR06.Area.Proposed

/-- The norm of every ordered tuple of individually normalized nonzero tensors
is exactly sqrt(r), independent of decomposition conditioning. -/
theorem normalizedTuple_norm_sq {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (a : Fin r → Tensor ℝ d n) (ha : ∀ i, a i ≠ 0) :
    ‖normalizedTuple a‖^2 = (r : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change ∑ iq : Fin r × TensorIndex d n, (a iq.1 iq.2 / ‖a iq.1‖)^2 = _
  rw [Fintype.sum_prod_type]
  have hi (i : Fin r) : (∑ q, (a i q / ‖a i‖)^2) = (1 : ℝ) := by
    simp_rw [div_pow,← Finset.sum_div]
    rw [← EuclideanSpace.real_norm_sq_eq]
    exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr (ha i)))
  simp_rw [hi]
  simp

theorem normalizedAnnularGraph_norm_lt {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    {z : NormalizedGraphAmbient d n r} (hz : z ∈ normalizedAnnularGraph d n r) :
    ‖z‖ < 4 + (r : ℝ) := by
  obtain ⟨_,_,hz3,a,ha,hout⟩ := hz
  have hs := WithLp.prod_norm_sq_eq_of_L2 z
  change ‖z‖^2 = ‖z.ofLp.1‖^2+‖z.ofLp.2‖^2 at hs
  rw [hout,normalizedTuple_norm_sq a (fun i => (ha.1 i).1)] at hs
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hz0 := norm_nonneg z.ofLp.1
  have hz0' := norm_nonneg z
  nlinarith

theorem euclideanNormalizedGraph_bounded {d : ℕ} {n : Fin d → ℕ} {r : ℕ} :
    Bornology.IsBounded (euclideanNormalizedGraph d n r) := by
  apply Metric.isBounded_iff_subset_ball (0 : Euclid (graphAmbientDimension d n r)) |>.mpr
  refine ⟨4+(r:ℝ),?_⟩
  rintro z ⟨w,hw,rfl⟩
  rw [Metric.mem_ball,dist_zero_right,(graphEuclideanEquiv d n r).norm_map]
  exact normalizedAnnularGraph_norm_lt hw

#assert_trust kernel normalizedTuple_norm_sq
#assert_trust kernel normalizedAnnularGraph_norm_lt
#assert_trust kernel euclideanNormalizedGraph_bounded
#print axioms euclideanNormalizedGraph_bounded
end NLA.Proofs.TR06
