/- Statement-only actual-definition/library inspection. No Challenge imported. -/
import NLA.RA09.Definitions
import LeanCert.Tactic.Verification
set_option pp.universes false
open scoped MatrixOrder
namespace NLA.RA09.StatementInspection
open NLA.RA09
#print ConcaveFrobeniusTransferConjecture
#print AdmissibleFunction
#print OrderedSpectralData
#print Matrix.PosSemidef
#print Matrix.le_iff
set_option pp.all true in
#print frobeniusNorm
set_option pp.all true in
#print functionalCalculus
#print frobeniusSquared
#print spectralCombination
#print truncation
#print functionTruncation
#print spectralTail
#print functionTail
#print overlapMatrix
#print overlapWeights
#print outerSquare
#print transferScale
#print scalarAuxiliary
#print branchQuadratic
#check Matrix.frobenius_norm_def
#check Matrix.trace_mul_comm
#check Matrix.trace_mul_cycle
#check Matrix.PosSemidef.dotProduct_mulVec_nonneg
#check Matrix.PosSemidef.conjTranspose_mul_mul_same
#check Matrix.PosSemidef.diag_nonneg
#check Matrix.PosSemidef.trace_nonneg
#check Matrix.IsHermitian.eigenvalues₀_antitone
#check Matrix.IsHermitian.spectral_theorem
#check Matrix.IsHermitian.mulVec_eigenvectorBasis
#check Matrix.PosSemidef.eigenvalues_nonneg
#check Matrix.IsHermitian.cfc_eq
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
#print axioms NLA.RA09.ConcaveFrobeniusTransferConjecture
#print axioms NLA.RA09.AdmissibleFunction
#print axioms NLA.RA09.OrderedSpectralData
#print axioms NLA.RA09.frobeniusSquared
#print axioms NLA.RA09.frobeniusNorm
#print axioms NLA.RA09.spectralCombination
#print axioms NLA.RA09.truncation
#print axioms NLA.RA09.functionalCalculus
#print axioms NLA.RA09.functionTruncation
#print axioms NLA.RA09.spectralTail
#print axioms NLA.RA09.functionTail
#print axioms NLA.RA09.overlapMatrix
#print axioms NLA.RA09.overlapWeights
#print axioms NLA.RA09.outerSquare
#print axioms NLA.RA09.transferScale
#print axioms NLA.RA09.scalarAuxiliary
#print axioms NLA.RA09.branchQuadratic
end NLA.RA09.StatementInspection
