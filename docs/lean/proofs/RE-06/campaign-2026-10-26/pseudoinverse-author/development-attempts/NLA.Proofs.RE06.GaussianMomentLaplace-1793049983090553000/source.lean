import NLA.Proofs.RE06.GaussianQuadratic
import NLA.Proofs.RE06.GaussianMomentGamma

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators ENNReal Topology

namespace NLA.Proofs.RE06.GaussianMoment

theorem scalar_inverse_laplace (x : ℝ) (hx : 0 < x) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-x * t))) = ENNReal.ofReal x⁻¹ := by
  have hi := integrableOn_exp_mul_Ioi (by linarith : -x < 0) (0 : ℝ)
  have he := integral_exp_mul_Ioi (by linarith : -x < 0) (0 : ℝ)
  have hh := (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun t => (Real.exp_pos (-x * t)).le))).symm
  simpa [he, div_eq_mul_inv] using hh

theorem affine_power_integral (p : ℝ) (hp : p < -1) :
    (∫ t : ℝ in Ioi 0, (2 * t + 1) ^ p) = -(1 / (2 * (p + 1))) := by
  have hp1 : p + 1 ≠ 0 := by linarith
  have hd : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => (2 * t + 1) ^ (p + 1) / (2 * (p + 1)))
        ((2 * x + 1) ^ p) x := by
    intro x hx
    convert! ((((hasDerivAt_id x).const_mul 2).add_const 1).rpow_const
      (Or.inl (by dsimp; linarith [mem_Ici.mp hx]))).div_const (2 * (p + 1)) using 1
    simp only [add_sub_cancel_right, id_eq]
    field_simp
  have haff : Tendsto (fun t : ℝ => 2 * t + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have ht : Tendsto (fun t : ℝ => (2 * t + 1) ^ (p + 1) / (2 * (p + 1)))
      atTop (𝓝 (0 / (2 * (p + 1)))) := by
    apply Tendsto.div_const
    simpa only [neg_neg] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < -(p + 1))).comp haff
  have hi := integrableOn_Ioi_deriv_of_nonneg' hd
    (fun x hx => Real.rpow_nonneg (by linarith [mem_Ioi.mp hx]) p) ht
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht
  simpa using he

#assert_trust kernel scalar_inverse_laplace
#assert_trust kernel affine_power_integral
#print axioms affine_power_integral
end NLA.Proofs.RE06.GaussianMoment
