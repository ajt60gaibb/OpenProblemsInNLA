/- Independent IS-03 statement inspection. No Challenge target is proved. -/
import Challenge
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import LeanCert.Tactic.Verification

set_option leancert.trust "kernel"

#print NLA.IS03.RealMatrix
#print NLA.IS03.EntrywiseNonnegative
#print NLA.IS03.normalizedDerivative
#print NLA.IS03.DerivativeRealizabilityConjecture
#print NLA.IS03.witnessMatrix
#print NLA.IS03.witnessPolynomial
#print NLA.IS03.derivativePolynomial
#print NLA.IS03.traceMoments

#print Matrix.trace
#print Matrix.charmatrix
#print Matrix.charpoly
#print Polynomial.derivative
#print Matrix.semiring
#synth Semiring (NLA.IS03.RealMatrix 6)
#synth Pow (NLA.IS03.RealMatrix 6) ℕ

set_option pp.all true in
#print NLA.IS03.EntrywiseNonnegative
set_option pp.all true in
#print NLA.IS03.normalizedDerivative
set_option pp.all true in
#print NLA.IS03.DerivativeRealizabilityConjecture
set_option pp.all true in
#check NLA.IS03.nonnegative_power_trace
set_option pp.all true in
#check NLA.IS03.trace_moment_certificate
set_option pp.all true in
#check NLA.IS03.negative_moment

#check NLA.IS03.witness_admissible
#check NLA.IS03.witness_polynomials
#check NLA.IS03.counterexample
#check NLA.IS03.not_derivativeRealizabilityConjecture

#check Matrix.mul_apply
#check Matrix.charpoly_fromBlocks_zero₁₂
#check Matrix.charpoly_reindex
#check Matrix.charpoly_natDegree_eq_dim
#check Matrix.charpoly_monic
#check Matrix.trace_eq_neg_charpoly_coeff
#check Matrix.trace_eq_sum_roots_charpoly_of_splits
#check Matrix.trace_eq_sum_roots_charpoly
#check Matrix.aeval_self_charpoly
#check Matrix.pow_eq_aeval_mod_charpoly
#check MvPolynomial.psum_eq_mul_esymm_sub_sum
#check MvPolynomial.aeval_esymm_eq_multiset_esymm
#check Polynomial.coeff_derivative

-- Only definitions are audited. These commands prove none of the seven targets.
#assert_trust kernel NLA.IS03.RealMatrix
#print axioms NLA.IS03.RealMatrix
#assert_trust kernel NLA.IS03.EntrywiseNonnegative
#print axioms NLA.IS03.EntrywiseNonnegative
#assert_trust kernel NLA.IS03.normalizedDerivative
#print axioms NLA.IS03.normalizedDerivative
#assert_trust kernel NLA.IS03.DerivativeRealizabilityConjecture
#print axioms NLA.IS03.DerivativeRealizabilityConjecture
#assert_trust kernel NLA.IS03.witnessMatrix
#print axioms NLA.IS03.witnessMatrix
#assert_trust kernel NLA.IS03.witnessPolynomial
#print axioms NLA.IS03.witnessPolynomial
#assert_trust kernel NLA.IS03.derivativePolynomial
#print axioms NLA.IS03.derivativePolynomial
#assert_trust kernel NLA.IS03.traceMoments
#print axioms NLA.IS03.traceMoments

-- Deliberately expose the admitted status rather than claiming theorem trust.
#print axioms NLA.IS03.trace_moment_certificate
#print axioms NLA.IS03.not_derivativeRealizabilityConjecture
