import NLA.Proofs.TR06.RetainedBoundaryMean

/-! Complete exact retained boundary and separate unchanged intrinsic Target.
Challenge is a comparison specification and is never imported. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.TR06

theorem target : NLA.Statements.TR06.Target := by
  exact NLA.Proofs.TR06.target

end NLA.TR06

#assert_trust kernel NLA.TR06.derivativeRatio_eq_operatorNorm
#assert_trust kernel NLA.TR06.angularSlope_eq_chart_derivative
#assert_trust kernel NLA.TR06.induced_volume_chart
#assert_trust kernel NLA.TR06.regular_locus
#assert_trust kernel NLA.TR06.finite_angular_mean
#assert_trust kernel NLA.TR06.generic_iff_source
#assert_trust kernel NLA.TR06.smooth_locus_correspondence
#assert_trust kernel NLA.TR06.smooth_chart_is_local_addition_inverse
#assert_trust kernel NLA.TR06.source_model_correspondence
#assert_trust kernel NLA.TR06.finite_angular_mean_source
#assert_trust kernel NLA.TR06.target

#print axioms NLA.TR06.derivativeRatio_eq_operatorNorm
#print axioms NLA.TR06.angularSlope_eq_chart_derivative
#print axioms NLA.TR06.induced_volume_chart
#print axioms NLA.TR06.regular_locus
#print axioms NLA.TR06.finite_angular_mean
#print axioms NLA.TR06.generic_iff_source
#print axioms NLA.TR06.smooth_locus_correspondence
#print axioms NLA.TR06.smooth_chart_is_local_addition_inverse
#print axioms NLA.TR06.source_model_correspondence
#print axioms NLA.TR06.finite_angular_mean_source
#print axioms NLA.TR06.target
