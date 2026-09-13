/- Independent RA-09 statement referee 2 inspection. Challenge is imported only
for reference signatures. No reference theorem is used as a mathematical premise.
No implementation is written or claimed. -/
import Challenge
import LeanCert.Tactic.Verification
set_option autoImplicit false
set_option pp.universes false
open scoped BigOperators Classical MatrixOrder
open NLA.RA09
#print NLA.RA09.frobeniusSquared
#print NLA.RA09.frobeniusNorm
#print NLA.RA09.AdmissibleFunction
#print NLA.RA09.OrderedSpectralData
#print NLA.RA09.spectralCombination
#print NLA.RA09.truncation
#print NLA.RA09.functionalCalculus
#print NLA.RA09.functionTruncation
#print NLA.RA09.spectralTail
#print NLA.RA09.functionTail
#print NLA.RA09.overlapMatrix
#print NLA.RA09.overlapWeights
#print NLA.RA09.outerSquare
#print NLA.RA09.transferScale
#print NLA.RA09.scalarAuxiliary
#print NLA.RA09.branchQuadratic
#print NLA.RA09.ConcaveFrobeniusTransferConjecture
set_option pp.all true in
#print NLA.RA09.frobeniusNorm
set_option pp.all true in
#print NLA.RA09.functionalCalculus
#print Matrix.PosSemidef
#print ConcaveOn
#print Matrix.instPreOrder
#check NLA.RA09.frobenius_semantics
#check NLA.RA09.frobenius_orthogonal_invariance
#check NLA.RA09.orderedSpectral_exists
#check NLA.RA09.orderedSpectral_semantics
#check NLA.RA09.functionalCalculus_spectral
#check NLA.RA09.truncation_semantics
#check NLA.RA09.trace_deficit_reduction
#check NLA.RA09.admissible_scalar_consequences
#check NLA.RA09.scalar_branch_certificates
#check NLA.RA09.ordered_scalar_certificate
#check NLA.RA09.harmonic_constraint
#check NLA.RA09.overlap_semantics
#check NLA.RA09.overlap_error_expansions
#check NLA.RA09.zero_column_average
#check NLA.RA09.positive_tail_transfer
#check NLA.RA09.zero_tail_closure
#check NLA.RA09.concaveFrobeniusTransferConjecture
#assert_trust kernel NLA.RA09.frobeniusSquared
#print axioms NLA.RA09.frobeniusSquared
#assert_trust kernel NLA.RA09.frobeniusNorm
#print axioms NLA.RA09.frobeniusNorm
#assert_trust kernel NLA.RA09.AdmissibleFunction
#print axioms NLA.RA09.AdmissibleFunction
#assert_trust kernel NLA.RA09.OrderedSpectralData
#print axioms NLA.RA09.OrderedSpectralData
#assert_trust kernel NLA.RA09.spectralCombination
#print axioms NLA.RA09.spectralCombination
#assert_trust kernel NLA.RA09.truncation
#print axioms NLA.RA09.truncation
#assert_trust kernel NLA.RA09.functionalCalculus
#print axioms NLA.RA09.functionalCalculus
#assert_trust kernel NLA.RA09.functionTruncation
#print axioms NLA.RA09.functionTruncation
#assert_trust kernel NLA.RA09.spectralTail
#print axioms NLA.RA09.spectralTail
#assert_trust kernel NLA.RA09.functionTail
#print axioms NLA.RA09.functionTail
#assert_trust kernel NLA.RA09.overlapMatrix
#print axioms NLA.RA09.overlapMatrix
#assert_trust kernel NLA.RA09.overlapWeights
#print axioms NLA.RA09.overlapWeights
#assert_trust kernel NLA.RA09.outerSquare
#print axioms NLA.RA09.outerSquare
#assert_trust kernel NLA.RA09.transferScale
#print axioms NLA.RA09.transferScale
#assert_trust kernel NLA.RA09.scalarAuxiliary
#print axioms NLA.RA09.scalarAuxiliary
#assert_trust kernel NLA.RA09.branchQuadratic
#print axioms NLA.RA09.branchQuadratic
#assert_trust kernel NLA.RA09.ConcaveFrobeniusTransferConjecture
#print axioms NLA.RA09.ConcaveFrobeniusTransferConjecture
#check Matrix.frobenius_norm_def
#assert_trust kernel Matrix.frobenius_norm_def
#print axioms Matrix.frobenius_norm_def
#check Matrix.posSemidef_iff_dotProduct_mulVec
#assert_trust kernel Matrix.posSemidef_iff_dotProduct_mulVec
#print axioms Matrix.posSemidef_iff_dotProduct_mulVec
#check Matrix.trace_mul_comm
#assert_trust kernel Matrix.trace_mul_comm
#print axioms Matrix.trace_mul_comm
#check Matrix.IsHermitian.eigenvalues₀_antitone
#assert_trust kernel Matrix.IsHermitian.eigenvalues₀_antitone
#print axioms Matrix.IsHermitian.eigenvalues₀_antitone
#check Matrix.IsHermitian.spectral_theorem
#assert_trust kernel Matrix.IsHermitian.spectral_theorem
#print axioms Matrix.IsHermitian.spectral_theorem
#check Matrix.IsHermitian.cfc_eq
#assert_trust kernel Matrix.IsHermitian.cfc_eq
#print axioms Matrix.IsHermitian.cfc_eq
#check Matrix.le_iff
#assert_trust kernel Matrix.le_iff
#print axioms Matrix.le_iff
#check concaveOn_iff_div
#assert_trust kernel concaveOn_iff_div
#print axioms concaveOn_iff_div
-- This last reference closure must visibly contain sorryAx at statement phase.
#print axioms NLA.RA09.concaveFrobeniusTransferConjecture
