import Challenge
import LeanCert.Tactic.Verification

set_option pp.universes true
set_option pp.proofs true
#print NLA.RA08.RealMatrix
#print NLA.RA08.spectralNorm
#print NLA.RA08.AdmissibleFunction
#print NLA.RA08.OrderedSpectralData
#print NLA.RA08.truncation
#print NLA.RA08.functionTruncation
#print NLA.RA08.functionalCalculus
#print NLA.RA08.ConcaveSpectralTransferConjecture
#print NLA.RA08.witnessMatrix
#print NLA.RA08.witnessF
#print NLA.RA08.matrixK
#print NLA.RA08.minorantFunction
#print NLA.RA08.minorantMatrix
#print NLA.RA08.witnessGap
#print Matrix.toEuclideanCLM
#print Matrix.PosSemidef
#print Matrix.unitaryGroup
#print Matrix.instPreOrder
#print ConcaveOn
#print MonotoneOn
set_option pp.all true in
#print NLA.RA08.spectralNorm
set_option pp.all true in
#print NLA.RA08.ConcaveSpectralTransferConjecture
set_option pp.all true in
#print NLA.RA08.spectral_tail_norms
set_option pp.all true in
#print NLA.RA08.minorant_functional_calculus

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
#check Matrix.IsHermitian.eigenvectorUnitary
#check Matrix.IsHermitian.spectral_theorem
#check Matrix.IsHermitian.cfc_eq
#check Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues
#check cfc_mono
#check cfc_polynomial
#check Matrix.PosSemidef.dotProduct_mulVec_zero_iff

-- These check definitions only; the fourteen Challenge holes prove nothing.
#assert_trust kernel NLA.RA08.spectralNorm
#assert_trust kernel NLA.RA08.AdmissibleFunction
#assert_trust kernel NLA.RA08.ConcaveSpectralTransferConjecture
#assert_trust kernel NLA.RA08.functionalCalculus
#assert_trust kernel NLA.RA08.witnessMatrix
#assert_trust kernel NLA.RA08.witnessGap
#print axioms NLA.RA08.spectralNorm
#print axioms NLA.RA08.AdmissibleFunction
#print axioms NLA.RA08.ConcaveSpectralTransferConjecture
#print axioms NLA.RA08.functionalCalculus
#print axioms NLA.RA08.witnessMatrix
#print axioms NLA.RA08.witnessGap
