import Challenge
import LeanCert.Tactic.Verification
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

set_option pp.universes true
set_option pp.proofs true

#print NLA.IS03.RealMatrix
#print NLA.IS03.EntrywiseNonnegative
#print NLA.IS03.normalizedDerivative
#print NLA.IS03.DerivativeRealizabilityConjecture
#print NLA.IS03.witnessMatrix
#print NLA.IS03.witnessPolynomial
#print NLA.IS03.derivativePolynomial
#print NLA.IS03.traceMoments
#print Matrix.charpoly
#print Matrix.charmatrix
#print Matrix.trace
#print Polynomial.derivative

set_option pp.all true in
#print NLA.IS03.normalizedDerivative
set_option pp.all true in
#print NLA.IS03.DerivativeRealizabilityConjecture
set_option pp.all true in
#print NLA.IS03.nonnegative_power_trace
set_option pp.all true in
#print NLA.IS03.trace_moment_certificate

#check NLA.IS03.nonnegative_power_trace
#check NLA.IS03.witness_admissible
#check NLA.IS03.witness_polynomials
#check NLA.IS03.trace_moment_certificate
#check NLA.IS03.negative_moment
#check NLA.IS03.counterexample
#check NLA.IS03.not_derivativeRealizabilityConjecture

-- Actual pinned library APIs, inspected only. No IS-03 proof is implemented here.
#check Matrix.charpoly_fromBlocks_zero₁₂
#check Matrix.charpoly_fromBlocks_zero₂₁
#check Matrix.charpoly_monic
#check Matrix.charpoly_natDegree_eq_dim
#check Matrix.trace_eq_neg_charpoly_coeff
#check Matrix.trace_eq_sum_roots_charpoly
#check Matrix.trace_eq_sum_roots_charpoly_of_splits
#check Matrix.aeval_self_charpoly
#check Matrix.pow_eq_aeval_mod_charpoly
#check Matrix.derivative_det_one_add_X_smul
#check MvPolynomial.psum_eq_mul_esymm_sub_sum
#check MvPolynomial.aeval_esymm_eq_multiset_esymm
#print MvPolynomial.psum

-- Definition-only checks do not certify the seven deliberately admitted targets.
#print axioms NLA.IS03.normalizedDerivative
#print axioms NLA.IS03.DerivativeRealizabilityConjecture
#print axioms NLA.IS03.witnessMatrix
#assert_trust kernel NLA.IS03.normalizedDerivative
#assert_trust kernel NLA.IS03.DerivativeRealizabilityConjecture
#assert_trust kernel NLA.IS03.witnessMatrix
