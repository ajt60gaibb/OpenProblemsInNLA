/- Independent statement inspection; no theorem implementation. -/
import Challenge

set_option pp.universes true
set_option pp.notation false
set_option pp.explicit false

#print CFC.abs
#print CFC.sqrt
#print Matrix.instPreOrder
#print Matrix.PosSemidef
#print Matrix.unitaryGroup
#check Matrix.le_iff
#check Matrix.star_eq_conjTranspose
#check Matrix.mem_unitaryGroup_iff
#check Matrix.mem_unitaryGroup_iff'
#check Matrix.posSemidef_iff_dotProduct_mulVec
#print Complex.normSq
#print Matrix.vecMulVec
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

#print axioms NLA.MI06.modulus_eq_sqrt
#print axioms NLA.MI06.witness_moduli
#print axioms NLA.MI06.two_vector_orthogonal
#print axioms NLA.MI06.witness_quadratic_bounds
#print axioms NLA.MI06.counterexample
#print axioms NLA.MI06.not_dominationConjecture
