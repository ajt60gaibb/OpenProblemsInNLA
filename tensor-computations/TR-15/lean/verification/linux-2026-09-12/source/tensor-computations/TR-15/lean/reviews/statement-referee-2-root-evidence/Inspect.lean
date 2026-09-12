/- Independent coordinating-agent statement inspection, before implementation. -/
import Challenge
import Mathlib.Topology.Order.IntermediateValue
import LeanCert.Tactic.Verification

set_option leancert.trust "kernel"
set_option pp.proofs false

#print NLA.TR15.Tensor
set_option pp.explicit true in
#print NLA.TR15.hankelTensor
set_option pp.explicit true in
#print NLA.TR15.contraction
set_option pp.explicit true in
#print NLA.TR15.IsHEigenpair
#print NLA.TR15.generatorIndex
#print NLA.TR15.prependIndex
#print NLA.TR15.lowerTensor
#print NLA.TR15.upperTensor
#print NLA.TR15.HasNoNegativeHEigenvalues
#print NLA.TR15.Admissible
#print NLA.TR15.InheritanceConjecture
#print NLA.TR15.witnessGenerator
#print NLA.TR15.rootPolynomial
#print NLA.TR15.lowerEigenvector
#print NLA.TR15.lowerEigenvalue
#check NLA.TR15.lower_contractions
#check NLA.TR15.upper_contraction
#check NLA.TR15.lower_eigenvalues_pos
#check NLA.TR15.lower_eigenpair_exists
#check NLA.TR15.upper_negative_eigenpair
#check NLA.TR15.counterexample
#check NLA.TR15.not_inheritanceConjecture
#check intermediate_value_Ioo
