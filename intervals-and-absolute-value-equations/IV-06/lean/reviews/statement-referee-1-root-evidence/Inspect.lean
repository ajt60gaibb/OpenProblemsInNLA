/- Independent root semantic inspector. Campaign printing/trust scaffolding reused; mathematical meanings independently checked. -/
import Challenge
import LeanCert.Tactic.Verification

set_option leancert.trust "kernel"
set_option pp.universes true
set_option pp.proofs true

#print NLA.IV06.EntrywiseLE
#print NLA.IV06.InIntervalFamily
#print NLA.IV06.HasRealEigenvalue
#print NLA.IV06.realEigenvalueSet
#print NLA.IV06.characteristicDet
#print NLA.IV06.componentCard
#print NLA.IV06.ComponentBoundConjecture
#print NLA.IV06.family
#print NLA.IV06.includedVector
#print NLA.IV06.separator
#print NLA.IV06.determinantLower
#print NLA.IV06.determinantUpper
#print ConnectedComponents
#print connectedComponentSetoid
#print ConnectedComponents.mk
#check ConnectedComponents.coe_eq_coe'
#check isPreconnected_connectedComponent
#check IsPreconnected.Icc_subset
#check Matrix.exists_mulVec_eq_zero_iff
#check Cardinal.mk_le_of_injective
#synth TopologicalSpace (NLA.IV06.realEigenvalueSet NLA.IV06.lower NLA.IV06.upper)
#synth OrderClosedTopology ℝ

set_option pp.all true in
#print NLA.IV06.HasRealEigenvalue

set_option pp.all true in
#print NLA.IV06.characteristicDet

set_option pp.all true in
#print NLA.IV06.componentCard

#check NLA.IV06.eigenvalue_determinant_semantics
#check NLA.IV06.family_and_determinant_semantics
#check NLA.IV06.witness_eigenpairs
#check NLA.IV06.witness_separators
#check NLA.IV06.connected_component_intervals
#check NLA.IV06.four_components
#check NLA.IV06.counterexample
#check NLA.IV06.not_componentBoundConjecture

-- Challenge placeholders intentionally have sorryAx; they establish no theorem.
#print axioms NLA.IV06.ComponentBoundConjecture
#print axioms NLA.IV06.characteristicDet
#print axioms NLA.IV06.componentCard

#assert_trust kernel NLA.IV06.ComponentBoundConjecture
#assert_trust kernel NLA.IV06.characteristicDet
#assert_trust kernel NLA.IV06.componentCard

#print Cardinal.mk
#print NLA.IV06.RealMatrix
#print NLA.IV06.lower
#print NLA.IV06.upper
