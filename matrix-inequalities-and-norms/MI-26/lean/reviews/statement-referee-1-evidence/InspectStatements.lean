/- Independent statement inspection only; no implementation theorem. -/
import Challenge

set_option pp.notation false
set_option pp.universes true

#print ConcaveOn
#print Matrix.IsHermitian.cfc
#check Matrix.IsHermitian.cfc_eq
#print Matrix.PosSemidef
#print Matrix.unitaryGroup
#check Matrix.le_iff
#check Matrix.mem_unitaryGroup_iff
#check Matrix.PosSemidef.eigenvalues_nonneg
#check Matrix.PosSemidef.dotProduct_mulVec_nonneg
#print NLA.MI26.AdmissibleFunction
#print NLA.MI26.unitaryConjugate
#print NLA.MI26.admissibleFunction_iff
#print NLA.MI26.functionalCalculus_eq_spectral
#print NLA.MI26.functionalCalculus_congr_nonneg
#print NLA.MI26.quadratic_cfc
#print NLA.MI26.witness_data
#print NLA.MI26.counterexample
#print NLA.MI26.not_subadditivityConjecture

set_option pp.explicit true in
#print NLA.MI26.functionalCalculus
set_option pp.explicit true in
#print NLA.MI26.SubadditivityConjecture

#print axioms NLA.MI26.admissibleFunction_iff
#print axioms NLA.MI26.functionalCalculus_eq_spectral
#print axioms NLA.MI26.functionalCalculus_congr_nonneg
#print axioms NLA.MI26.quadratic_cfc
#print axioms NLA.MI26.witness_data
#print axioms NLA.MI26.counterexample
#print axioms NLA.MI26.not_subadditivityConjecture
