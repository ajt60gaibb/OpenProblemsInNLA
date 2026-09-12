import Challenge
set_option pp.explicit true
set_option pp.notation false
set_option pp.proofs false
#print NLA.MI23.spectralPower
#print NLA.MI23.generalizedMean
#print NLA.MI23.orderedEigenvalues
#print NLA.MI23.HasOrderedPositiveEigenvalues
#print NLA.MI23.LogMajorized
#print NLA.MI23.largestEigenvalue
#print NLA.MI23.leftProduct
#print NLA.MI23.rightProduct
#print NLA.MI23.GeneralizedGeometricMeanConjecture
#print NLA.MI23.operatorNorm
#print NLA.MI23.frobeniusSquared
set_option pp.explicit false
set_option pp.notation true
#check NLA.MI23.positive_powers_and_means
#check NLA.MI23.product_eigenvalue_semantics
#check NLA.MI23.squared_product_largest
#check NLA.MI23.operator_norm_bounds
#check NLA.MI23.witness_data
#check NLA.MI23.witness_squared_gap
#check NLA.MI23.counterexample
#check NLA.MI23.not_generalizedGeometricMeanConjecture
#check Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀
#check Matrix.IsHermitian.roots_charpoly_eq_eigenvalues₀
#check Matrix.charpoly_mul_comm
#check Matrix.PosDef.eigenvalues_pos
#check Matrix.l2_opNorm_conjTranspose_mul_self
#check CFC.rpow_rpow
#check CFC.rpow_natCast
#check CFC.rpow_neg_mul_rpow
#check CFC.rpow_mul_rpow_neg
