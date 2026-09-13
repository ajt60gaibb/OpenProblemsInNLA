/- Independent IS03 statement referee 1 inspection. No Challenge proof is implemented. -/
import Challenge
import LeanCert.Tactic.Verification
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

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
#print Matrix.mul_apply
#check @pow_succ (NLA.IS03.RealMatrix 6) _
#check Matrix.charpoly_isEmpty
#check Matrix.trace_eq_zero_of_isEmpty
#check Matrix.trace_one
#check Polynomial.coeff_derivative
#check Matrix.charpoly_monic
#check Matrix.charpoly_natDegree_eq_dim
#check Matrix.eval_charpoly
#check Matrix.trace_eq_sum_roots_charpoly
#check Matrix.trace_eq_sum_roots_charpoly_of_splits

set_option pp.all true in
#print NLA.IS03.normalizedDerivative
set_option pp.all true in
#print NLA.IS03.DerivativeRealizabilityConjecture
set_option pp.all true in
#print NLA.IS03.nonnegative_power_trace
set_option pp.all true in
#print NLA.IS03.trace_moment_certificate
set_option pp.all true in
#print NLA.IS03.counterexample
set_option pp.all true in
#print NLA.IS03.negative_moment

#check NLA.IS03.nonnegative_power_trace
#check NLA.IS03.witness_admissible
#check NLA.IS03.witness_polynomials
#check NLA.IS03.trace_moment_certificate
#check NLA.IS03.negative_moment
#check NLA.IS03.counterexample
#check NLA.IS03.not_derivativeRealizabilityConjecture

-- Concrete definitions only. These twelve audits do not certify the seven holes.
#assert_trust kernel NLA.IS03.RealMatrix
#assert_trust kernel NLA.IS03.EntrywiseNonnegative
#assert_trust kernel NLA.IS03.normalizedDerivative
#assert_trust kernel NLA.IS03.DerivativeRealizabilityConjecture
#assert_trust kernel NLA.IS03.witnessMatrix
#assert_trust kernel NLA.IS03.witnessPolynomial
#assert_trust kernel NLA.IS03.derivativePolynomial
#assert_trust kernel NLA.IS03.traceMoments
#assert_trust kernel Matrix.charpoly
#assert_trust kernel Matrix.charmatrix
#assert_trust kernel Matrix.trace
#assert_trust kernel Polynomial.derivative
#print axioms NLA.IS03.RealMatrix
#print axioms NLA.IS03.EntrywiseNonnegative
#print axioms NLA.IS03.normalizedDerivative
#print axioms NLA.IS03.DerivativeRealizabilityConjecture
#print axioms NLA.IS03.witnessMatrix
#print axioms NLA.IS03.witnessPolynomial
#print axioms NLA.IS03.derivativePolynomial
#print axioms NLA.IS03.traceMoments
#print axioms Matrix.charpoly
#print axioms Matrix.charmatrix
#print axioms Matrix.trace
#print axioms Polynomial.derivative
