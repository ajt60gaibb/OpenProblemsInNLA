import NLA.Proofs.RE05.GaussianQuadraticCovariance
set_option leancert.trust "kernel"
namespace RE05QuadraticNegative
theorem rejected : False := by sorry
#assert_trust kernel rejected
end RE05QuadraticNegative
