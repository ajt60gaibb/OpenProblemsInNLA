import Solution

/- Inspect the actual Boolean-checker equality, separately from the precision
inequality in the outer certificate. This is audit code, not a proof change. -/
#assert_trust kernel NLA.TR15.negative_eigenvalue_certificate._proof_1_7
#print axioms NLA.TR15.negative_eigenvalue_certificate._proof_1_7
set_option pp.proofs true in
#print NLA.TR15.negative_eigenvalue_certificate._proof_1_7
