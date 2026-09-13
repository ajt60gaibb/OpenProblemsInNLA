import Challenge
import LeanCert.Tactic.Verification

/- Independent statement referee 1: actual signatures and instance-bearing
definitions. No Challenge theorem is used as a proof or trust-audited here. -/
set_option pp.universes true
set_option pp.proofs true

#print NLA.RA08.RealMatrix
#print NLA.RA08.OrderedSpectralData
#print NLA.RA08.AdmissibleFunction
#print NLA.RA08.spectralCombination
#print NLA.RA08.truncation
#print NLA.RA08.functionTruncation
#print NLA.RA08.functionalCalculus
#print NLA.RA08.witnessF
#print NLA.RA08.witnessMatrix
#print NLA.RA08.matrixK
#print NLA.RA08.minorantFunction
#print NLA.RA08.minorantMatrix
#print NLA.RA08.witnessGap
#print Matrix.toEuclideanCLM
#print Matrix.instPreOrder
#print Matrix.PosSemidef
#print Matrix.unitaryGroup
#print ConcaveOn
#print MonotoneOn

set_option pp.all true in
#print NLA.RA08.spectralNorm
set_option pp.all true in
#print NLA.RA08.functionalCalculus
set_option pp.all true in
#print NLA.RA08.ConcaveSpectralTransferConjecture
set_option pp.all true in
#print NLA.RA08.functionTruncation
set_option pp.all true in
#print NLA.RA08.minorantMatrix

#check NLA.RA08.orderedSpectral_exists
#check NLA.RA08.orderedSpectral_semantics
#check NLA.RA08.functionalCalculus_spectral
#check NLA.RA08.spectral_tail_norms
#check NLA.RA08.operator_rayleigh_bound
#check NLA.RA08.witness_data
#check NLA.RA08.witness_spectral_location
#check NLA.RA08.minorant_scalar
#check NLA.RA08.minorant_functional_calculus
#check NLA.RA08.witness_tail_data
#check NLA.RA08.witness_rational_certificate
#check NLA.RA08.numerical_gap_positive
#check NLA.RA08.counterexample
#check NLA.RA08.not_concaveSpectralTransferConjecture

#check Matrix.IsHermitian.eigenvalues₀_antitone
#check Matrix.IsHermitian.spectral_theorem
#check Matrix.IsHermitian.cfc_eq
#check Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues
#check cfc_mono
#check cfc_polynomial
#check Matrix.l2_opNorm_toEuclideanCLM
#check Matrix.l2_opNorm_diagonal

-- Definitions only: these checks cannot certify any of the fourteen holes.
#assert_trust kernel NLA.RA08.spectralNorm
#print axioms NLA.RA08.spectralNorm
#assert_trust kernel NLA.RA08.AdmissibleFunction
#print axioms NLA.RA08.AdmissibleFunction
#assert_trust kernel NLA.RA08.OrderedSpectralData
#print axioms NLA.RA08.OrderedSpectralData
#assert_trust kernel NLA.RA08.functionalCalculus
#print axioms NLA.RA08.functionalCalculus
#assert_trust kernel NLA.RA08.functionTruncation
#print axioms NLA.RA08.functionTruncation
#assert_trust kernel NLA.RA08.ConcaveSpectralTransferConjecture
#print axioms NLA.RA08.ConcaveSpectralTransferConjecture
#assert_trust kernel NLA.RA08.minorantMatrix
#print axioms NLA.RA08.minorantMatrix
#assert_trust kernel NLA.RA08.witnessGap
#print axioms NLA.RA08.witnessGap
