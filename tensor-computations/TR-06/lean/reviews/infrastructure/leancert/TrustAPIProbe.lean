import LeanCert.Tactic.Verification
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/- Development API audit only. No new mathematical theorem or numerical certificate. -/
set_option leancert.trust "kernel"
#check LeanCert.Tactic.VerificationMode.kernel
#check LeanCert.Tactic.VerificationConfig.current
#check LeanCert.Tactic.closeCertificateGoalTyped
#check LeanCert.Tactic.withTrustMode
#check LeanCert.Tactic.classifyAxiom
#assert_trust kernel integrableOn_rpow_mul_exp_neg_mul_sq
#print axioms integrableOn_rpow_mul_exp_neg_mul_sq
