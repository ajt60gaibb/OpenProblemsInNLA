/- Independent statement inspection only: no IV-06 theorem is proved here. -/
import Challenge
import LeanCert.Tactic.Verification

set_option leancert.trust "kernel"
set_option pp.universes true

#print NLA.IV06.EntrywiseLE
#print NLA.IV06.InIntervalFamily
#print NLA.IV06.HasRealEigenvalue
#print NLA.IV06.realEigenvalueSet
#print NLA.IV06.characteristicDet
#print NLA.IV06.componentCard
#print NLA.IV06.ComponentBoundConjecture
#print NLA.IV06.family
#print NLA.IV06.lower
#print NLA.IV06.upper
#print NLA.IV06.includedValue
#print NLA.IV06.includedA
#print NLA.IV06.includedB
#print NLA.IV06.includedVector
#print NLA.IV06.separator
#print NLA.IV06.determinantLower
#print NLA.IV06.determinantUpper

#print ConnectedComponents
#print connectedComponentSetoid
#print connectedComponent
#print ConnectedComponents.mk
#check ConnectedComponents.coe_eq_coe'
#check mem_connectedComponent
#check isPreconnected_connectedComponent
#check IsPreconnected.image
#check continuous_subtype_val
#check IsPreconnected.Icc_subset
#check Matrix.exists_mulVec_eq_zero_iff
#check Cardinal.mk_le_of_injective
#check Cardinal.mk_fin
#check Matrix.det_isEmpty

#synth TopologicalSpace ℝ
#synth TopologicalSpace (NLA.IV06.realEigenvalueSet NLA.IV06.lower NLA.IV06.upper)
#synth OrderClosedTopology ℝ

set_option pp.all true in
#print NLA.IV06.HasRealEigenvalue

set_option pp.all true in
#print NLA.IV06.characteristicDet

set_option pp.all true in
#print NLA.IV06.componentCard

set_option pp.all true in
#print NLA.IV06.ComponentBoundConjecture

#check NLA.IV06.eigenvalue_determinant_semantics
#check NLA.IV06.family_and_determinant_semantics
#check NLA.IV06.witness_eigenpairs
#check NLA.IV06.witness_separators
#check NLA.IV06.connected_component_intervals
#check NLA.IV06.four_components
#check NLA.IV06.counterexample
#check NLA.IV06.not_componentBoundConjecture

#assert_trust kernel NLA.IV06.ComponentBoundConjecture
#print axioms NLA.IV06.ComponentBoundConjecture
#assert_trust kernel NLA.IV06.characteristicDet
#print axioms NLA.IV06.characteristicDet
#assert_trust kernel NLA.IV06.componentCard
#print axioms NLA.IV06.componentCard

-- These two deliberately expose sorryAx: statement elaboration proves nothing.
#print axioms NLA.IV06.eigenvalue_determinant_semantics
#print axioms NLA.IV06.not_componentBoundConjecture
