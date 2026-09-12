/- Statement inspection only. No mathematical proof is implemented here. -/
import Challenge

set_option pp.universes true
set_option pp.notation false

#print CFC.abs
#print Matrix.instPreOrder
#print Matrix.PosSemidef
#print Matrix.unitaryGroup
#check Matrix.le_iff
#check Matrix.posSemidef_iff_dotProduct_mulVec
#check Matrix.mem_unitaryGroup_iff
#print Complex.normSq
#print NLA.MI06.matrixModulus
#print NLA.MI06.symmetricModulus
#print NLA.MI06.unitaryConjugate
#print NLA.MI06.DominationConjecture
#print NLA.MI06.squaredLength
#print NLA.MI06.quadraticForm
#print NLA.MI06.rankOne
#check NLA.MI06.modulus_eq_sqrt
#check NLA.MI06.witness_moduli
#check NLA.MI06.two_vector_orthogonal
#check NLA.MI06.witness_quadratic_bounds
#check NLA.MI06.counterexample
#check NLA.MI06.not_dominationConjecture

/- The six Challenge placeholders should depend on sorryAx at this stage. -/
#print axioms NLA.MI06.modulus_eq_sqrt
#print axioms NLA.MI06.witness_moduli
#print axioms NLA.MI06.two_vector_orthogonal
#print axioms NLA.MI06.witness_quadratic_bounds
#print axioms NLA.MI06.counterexample
#print axioms NLA.MI06.not_dominationConjecture
