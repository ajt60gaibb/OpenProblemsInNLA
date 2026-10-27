import NLA.Proofs.RE05.OneCopyError
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace RE05OneCopyNegative
/-- Deliberate proof contamination must fail the kernel trust assertion. -/
theorem forged_relative_error : False := by sorry
#assert_trust kernel forged_relative_error
end RE05OneCopyNegative
