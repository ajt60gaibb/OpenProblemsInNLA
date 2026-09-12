/- Independent semantic inspection, not a proof implementation. -/
import Challenge
import LeanCert.Tactic.Verification
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option leancert.trust "kernel"
set_option pp.explicit true
set_option pp.universes true
open scoped BigOperators Classical ComplexOrder MatrixOrder

#print NLA.MI03.Mat
#assert_trust kernel NLA.MI03.Mat
#print axioms NLA.MI03.Mat

#print NLA.MI03.matrixModulus
#assert_trust kernel NLA.MI03.matrixModulus
#print axioms NLA.MI03.matrixModulus

#print NLA.MI03.operatorNorm
#assert_trust kernel NLA.MI03.operatorNorm
#print axioms NLA.MI03.operatorNorm

#print NLA.MI03.summandSum
#assert_trust kernel NLA.MI03.summandSum
#print axioms NLA.MI03.summandSum

#print NLA.MI03.modulusSum
#assert_trust kernel NLA.MI03.modulusSum
#print axioms NLA.MI03.modulusSum

#print NLA.MI03.errorGap
#assert_trust kernel NLA.MI03.errorGap
#print axioms NLA.MI03.errorGap

#print NLA.MI03.AdmissibleConstant
#assert_trust kernel NLA.MI03.AdmissibleConstant
#print axioms NLA.MI03.AdmissibleConstant

#print NLA.MI03.admissibleConstants
#assert_trust kernel NLA.MI03.admissibleConstants
#print axioms NLA.MI03.admissibleConstants

#print NLA.MI03.sharpConstant
#assert_trust kernel NLA.MI03.sharpConstant
#print axioms NLA.MI03.sharpConstant

#print NLA.MI03.OddContractionConjecture
#assert_trust kernel NLA.MI03.OddContractionConjecture
#print axioms NLA.MI03.OddContractionConjecture

#print NLA.MI03.pairVariance
#assert_trust kernel NLA.MI03.pairVariance
#print axioms NLA.MI03.pairVariance

#print NLA.MI03.shiftedSquare
#assert_trust kernel NLA.MI03.shiftedSquare
#print axioms NLA.MI03.shiftedSquare

#print NLA.MI03.rootOfUnity
#assert_trust kernel NLA.MI03.rootOfUnity
#print axioms NLA.MI03.rootOfUnity

#print NLA.MI03.firstVector
#assert_trust kernel NLA.MI03.firstVector
#print axioms NLA.MI03.firstVector

#print NLA.MI03.witnessVector
#assert_trust kernel NLA.MI03.witnessVector
#print axioms NLA.MI03.witnessVector

#print NLA.MI03.outerProduct
#assert_trust kernel NLA.MI03.outerProduct
#print axioms NLA.MI03.outerProduct

#print NLA.MI03.witness
#assert_trust kernel NLA.MI03.witness
#print axioms NLA.MI03.witness

#print NLA.MI03.firstProjection
#assert_trust kernel NLA.MI03.firstProjection
#print axioms NLA.MI03.firstProjection

#print NLA.MI03.witnessModulusSum
#assert_trust kernel NLA.MI03.witnessModulusSum
#print axioms NLA.MI03.witnessModulusSum

#print NLA.MI03.witnessDifference
#assert_trust kernel NLA.MI03.witnessDifference
#print axioms NLA.MI03.witnessDifference

#check NLA.MI03.modulus_semantics
#print axioms NLA.MI03.modulus_semantics

#check NLA.MI03.contraction_modulus
#print axioms NLA.MI03.contraction_modulus

#check NLA.MI03.positive_decomposition
#print axioms NLA.MI03.positive_decomposition

#check NLA.MI03.universal_upper_bound
#print axioms NLA.MI03.universal_upper_bound

#check NLA.MI03.root_of_unity_data
#print axioms NLA.MI03.root_of_unity_data

#check NLA.MI03.sharpness_witness
#print axioms NLA.MI03.sharpness_witness

#check NLA.MI03.sharp_constant
#print axioms NLA.MI03.sharp_constant

#check NLA.MI03.odd_contraction_conjecture
#print axioms NLA.MI03.odd_contraction_conjecture


#print Matrix.PosSemidef
#print Matrix.instPartialOrder
#print Matrix.le_iff
#print Complex.le_def
#print Matrix.toEuclideanCLM
#print CFC.sqrt
#print CFC.abs
#print IsLeast
#check IsLeast.csInf_eq
#check Matrix.posSemidef_conjTranspose_mul_self
#check CFC.sqrt_mul_sqrt_self
#check CFC.sqrt_unique
#check CFC.abs_mul_abs
#check CFC.norm_abs
#check CStarAlgebra.norm_le_one_iff_of_nonneg
#check Matrix.l2_opNorm_toEuclideanCLM
#check Matrix.toEuclideanCLM_toLp
#check EuclideanSpace.norm_sq_eq
#check InnerProductSpace.norm_rankOne
#check InnerProductSpace.symm_toEuclideanLin_rankOne
#check Complex.isPrimitiveRoot_exp
#check IsPrimitiveRoot.norm'_eq_one
#check IsPrimitiveRoot.geom_sum_eq_zero
#synth PartialOrder (NLA.MI03.Mat 2)
#synth Norm (EuclideanSpace ℂ (Fin 2))
set_option pp.all true in
#print NLA.MI03.operatorNorm
set_option pp.all true in
#print NLA.MI03.matrixModulus
set_option pp.all true in
#print NLA.MI03.OddContractionConjecture
set_option pp.all true in
#check NLA.MI03.sharpness_witness
set_option pp.all true in
#check NLA.MI03.sharp_constant
