import NLA.Proofs.RE05.RegressionSolveTransport
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace RE05RegressionNegative
/-- Deliberate proof contamination: the kernel trust checker must reject it. -/
theorem forged_full_rank : False := by sorry
#assert_trust kernel forged_full_rank
end RE05RegressionNegative
