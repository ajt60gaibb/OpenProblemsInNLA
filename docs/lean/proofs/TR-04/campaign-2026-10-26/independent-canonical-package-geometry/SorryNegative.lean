import LeanCert.Tactic.Verification
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace IndependentCanonicalSorryControlGeometry
theorem deliberately_invalid : False := by sorry
#print axioms deliberately_invalid
#assert_trust kernel deliberately_invalid
end IndependentCanonicalSorryControlGeometry
