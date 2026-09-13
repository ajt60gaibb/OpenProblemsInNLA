/- Independent root statement inspection; no Challenge or implementation import. -/
import NLA.RA09.Definitions
import LeanCert.Tactic.Verification

set_option autoImplicit false
open scoped BigOperators Classical MatrixOrder
namespace NLA.RA09.RootStatementInspection
open NLA.RA09 Matrix

set_option pp.all true in
#print frobeniusNorm
set_option pp.all true in
#print functionalCalculus
#print ConcaveFrobeniusTransferConjecture
#print AdmissibleFunction
#print OrderedSpectralData
#print frobeniusSquared
#print truncation
#print functionTruncation
#print spectralTail
#print functionTail
#print overlapWeights
#print scalarAuxiliary
#print Matrix.PosSemidef
#print Matrix.le_iff
#check Matrix.frobenius_norm_def
#check Matrix.PosSemidef.dotProduct_mulVec_nonneg
#check Matrix.PosSemidef.mul_mul_conjTranspose_same
#check Matrix.PosSemidef.diag_nonneg
#check Matrix.trace_mul_cycle
#check Matrix.IsHermitian.eigenvalues₀_antitone
#check Matrix.IsHermitian.spectral_theorem
#check Matrix.PosSemidef.eigenvalues_nonneg
#check Matrix.IsHermitian.cfc_eq
#check cfcHom_eq_of_continuous_of_map_id
#check concaveOn_iff_div

#assert_trust kernel ConcaveFrobeniusTransferConjecture
#assert_trust kernel AdmissibleFunction
#assert_trust kernel OrderedSpectralData
#assert_trust kernel frobeniusSquared
#assert_trust kernel frobeniusNorm
#assert_trust kernel spectralCombination
#assert_trust kernel truncation
#assert_trust kernel functionalCalculus
#assert_trust kernel functionTruncation
#assert_trust kernel spectralTail
#assert_trust kernel functionTail
#assert_trust kernel overlapMatrix
#assert_trust kernel overlapWeights
#assert_trust kernel outerSquare
#assert_trust kernel transferScale
#assert_trust kernel scalarAuxiliary
#assert_trust kernel branchQuadratic
#print axioms ConcaveFrobeniusTransferConjecture
#print axioms AdmissibleFunction
#print axioms OrderedSpectralData
#print axioms frobeniusSquared
#print axioms frobeniusNorm
#print axioms spectralCombination
#print axioms truncation
#print axioms functionalCalculus
#print axioms functionTruncation
#print axioms spectralTail
#print axioms functionTail
#print axioms overlapMatrix
#print axioms overlapWeights
#print axioms outerSquare
#print axioms transferScale
#print axioms scalarAuxiliary
#print axioms branchQuadratic
end NLA.RA09.RootStatementInspection
