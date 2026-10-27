import NLA.Proofs.RE05.OffsetContraction
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace RE05CenteredOffsetNegative
/-- Deliberate contamination tests kernel rejection, never a producer proof. -/
theorem forged_variance : False := by sorry
#assert_trust kernel forged_variance
end RE05CenteredOffsetNegative
