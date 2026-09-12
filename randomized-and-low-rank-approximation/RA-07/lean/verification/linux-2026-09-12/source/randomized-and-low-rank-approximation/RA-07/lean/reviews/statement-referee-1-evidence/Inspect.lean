import Challenge
import LeanCert.Tactic.Verification
set_option pp.proofs false
set_option pp.universes false
set_option pp.fullNames true
#print NLA.RA07.elementarySymmetric
#assert_trust kernel NLA.RA07.elementarySymmetric
#print axioms NLA.RA07.elementarySymmetric
#print NLA.RA07.errorSequence
#assert_trust kernel NLA.RA07.errorSequence
#print axioms NLA.RA07.errorSequence
#print NLA.RA07.generatingPolynomial
#assert_trust kernel NLA.RA07.generatingPolynomial
#print axioms NLA.RA07.generatingPolynomial
#print NLA.RA07.iteratedGeneratingDerivative
#assert_trust kernel NLA.RA07.iteratedGeneratingDerivative
#print axioms NLA.RA07.iteratedGeneratingDerivative
#print NLA.RA07.powerSum
#assert_trust kernel NLA.RA07.powerSum
#print axioms NLA.RA07.powerSum
#print NLA.RA07.pairGap
#assert_trust kernel NLA.RA07.pairGap
#print axioms NLA.RA07.pairGap
#print NLA.RA07.certificateDenominator
#assert_trust kernel NLA.RA07.certificateDenominator
#print axioms NLA.RA07.certificateDenominator
#print NLA.RA07.ConvexityConjecture
#assert_trust kernel NLA.RA07.ConvexityConjecture
#print axioms NLA.RA07.ConvexityConjecture
#print NLA.RA07.elementary_values
#print axioms NLA.RA07.elementary_values
#print NLA.RA07.generating_derivative_values
#print axioms NLA.RA07.generating_derivative_values
#print NLA.RA07.positive_derivative_factorization
#print axioms NLA.RA07.positive_derivative_factorization
#print NLA.RA07.power_sum_certificate
#print axioms NLA.RA07.power_sum_certificate
#print NLA.RA07.second_difference_certificate
#print axioms NLA.RA07.second_difference_certificate
#print NLA.RA07.errorSequence_convex
#print axioms NLA.RA07.errorSequence_convex
#check Finset.mem_powersetCard
#check Finset.esymm_map_val
#check Polynomial.coeff_iterate_derivative
#check Polynomial.natDegree_iterate_derivative
