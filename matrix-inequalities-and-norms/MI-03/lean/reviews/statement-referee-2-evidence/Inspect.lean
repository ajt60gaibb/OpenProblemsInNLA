/- Independent MI-03 statement referee 2. Declarations and primary APIs only;
no Challenge theorem is asserted or supplied with a proof. -/
import Challenge
import LeanCert.Tactic.Verification

set_option leancert.trust "kernel"

#print NLA.MI03.Mat
#print NLA.MI03.matrixModulus
#print NLA.MI03.operatorNorm
#print NLA.MI03.summandSum
#print NLA.MI03.modulusSum
#print NLA.MI03.errorGap
#print NLA.MI03.AdmissibleConstant
#print NLA.MI03.admissibleConstants
#print NLA.MI03.sharpConstant
#print NLA.MI03.OddContractionConjecture
#print NLA.MI03.pairVariance
#print NLA.MI03.shiftedSquare
#print NLA.MI03.rootOfUnity
#print NLA.MI03.firstVector
#print NLA.MI03.witnessVector
#print NLA.MI03.outerProduct
#print NLA.MI03.witness
#print NLA.MI03.firstProjection
#print NLA.MI03.witnessModulusSum
#print NLA.MI03.witnessDifference

set_option pp.explicit true in
#print NLA.MI03.matrixModulus
set_option pp.explicit true in
#print NLA.MI03.operatorNorm
set_option pp.explicit true in
#print NLA.MI03.shiftedSquare
set_option pp.explicit true in
#print NLA.MI03.outerProduct
set_option pp.explicit true in
#print NLA.MI03.AdmissibleConstant
set_option pp.explicit true in
#check NLA.MI03.sharpness_witness

#print Matrix.PosSemidef
#print CFC.sqrt
#check Matrix.nonneg_iff_posSemidef
#check CFC.sqrt_mul_sqrt_self
#check CFC.sqrt_unique
#check CFC.sqrt_zero
#check Complex.isPrimitiveRoot_exp
#check IsPrimitiveRoot.geom_sum_eq_zero
#check IsLeast.csInf_eq
#check Matrix.toEuclideanCLM_toLp

#check NLA.MI03.modulus_semantics
#check NLA.MI03.contraction_modulus
#check NLA.MI03.positive_decomposition
#check NLA.MI03.universal_upper_bound
#check NLA.MI03.root_of_unity_data
#check NLA.MI03.sharpness_witness
#check NLA.MI03.sharp_constant
#check NLA.MI03.odd_contraction_conjecture

#assert_trust kernel NLA.MI03.Mat
#print axioms NLA.MI03.Mat

#assert_trust kernel NLA.MI03.matrixModulus
#print axioms NLA.MI03.matrixModulus

#assert_trust kernel NLA.MI03.operatorNorm
#print axioms NLA.MI03.operatorNorm

#assert_trust kernel NLA.MI03.summandSum
#print axioms NLA.MI03.summandSum

#assert_trust kernel NLA.MI03.modulusSum
#print axioms NLA.MI03.modulusSum

#assert_trust kernel NLA.MI03.errorGap
#print axioms NLA.MI03.errorGap

#assert_trust kernel NLA.MI03.AdmissibleConstant
#print axioms NLA.MI03.AdmissibleConstant

#assert_trust kernel NLA.MI03.admissibleConstants
#print axioms NLA.MI03.admissibleConstants

#assert_trust kernel NLA.MI03.sharpConstant
#print axioms NLA.MI03.sharpConstant

#assert_trust kernel NLA.MI03.OddContractionConjecture
#print axioms NLA.MI03.OddContractionConjecture

#assert_trust kernel NLA.MI03.pairVariance
#print axioms NLA.MI03.pairVariance

#assert_trust kernel NLA.MI03.shiftedSquare
#print axioms NLA.MI03.shiftedSquare

#assert_trust kernel NLA.MI03.rootOfUnity
#print axioms NLA.MI03.rootOfUnity

#assert_trust kernel NLA.MI03.firstVector
#print axioms NLA.MI03.firstVector

#assert_trust kernel NLA.MI03.witnessVector
#print axioms NLA.MI03.witnessVector

#assert_trust kernel NLA.MI03.outerProduct
#print axioms NLA.MI03.outerProduct

#assert_trust kernel NLA.MI03.witness
#print axioms NLA.MI03.witness

#assert_trust kernel NLA.MI03.firstProjection
#print axioms NLA.MI03.firstProjection

#assert_trust kernel NLA.MI03.witnessModulusSum
#print axioms NLA.MI03.witnessModulusSum

#assert_trust kernel NLA.MI03.witnessDifference
#print axioms NLA.MI03.witnessDifference
