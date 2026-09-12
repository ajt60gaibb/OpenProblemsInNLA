/- Explicit actual-instance inspection of the completed solution. -/
import Solution

set_option pp.universes true
set_option pp.notation false
set_option pp.explicit true

#print CFC.abs
#print CFC.sqrt
#check CFC.sqrt_unique
#print Matrix.instPreOrder
#print Matrix.PosSemidef
#print Matrix.unitaryGroup
#check Matrix.le_iff
#check Matrix.star_eq_conjTranspose
#check Matrix.mem_unitaryGroup_iff
#check Matrix.PosSemidef.dotProduct_mulVec_nonneg
#check LinearMap.finrank_le_finrank_of_injective
#print NLA.MI06.matrixModulus
#print NLA.MI06.symmetricModulus
#print NLA.MI06.unitaryConjugate
#print NLA.MI06.DominationConjecture
#print NLA.MI06.squaredLength
#print NLA.MI06.quadraticForm
#print NLA.MI06.rankOne
#print NLA.MI06.modulus_eq_sqrt
#print NLA.MI06.witness_moduli
#print NLA.MI06.two_vector_orthogonal
#print NLA.MI06.witness_quadratic_bounds
#print NLA.MI06.counterexample
#print NLA.MI06.not_dominationConjecture
