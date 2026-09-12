import Challenge
import LeanCert.Tactic.Verification

set_option pp.all true
#print NLA.IE23.euclideanNorm
#print NLA.IE23.lpNorm
#print NLA.IE23.ratioSet
#print NLA.IE23.inducedNorm
#print NLA.IE23.FullRowRank
#print NLA.IE23.moorePenrose
#print NLA.IE23.IsNormMinimizer
#print NLA.IE23.RightInverseUniqueConjecture
set_option pp.all false
#print EuclideanSpace
#print Matrix.rank
#print Matrix.inv
#print Real.rpow
#check EuclideanSpace.norm_sq_eq
#check Real.rpow_pos_of_pos
#check csSup_le
#check le_csSup
#check NLA.IE23.inducedNorm_semantics
#check NLA.IE23.witness_matrix_identities
#check NLA.IE23.fourth_power_norm_control
#check NLA.IE23.witness_action_identities
#check NLA.IE23.witness_attainment
#check NLA.IE23.witness_norms
#check NLA.IE23.witness_global_minimizers
#check NLA.IE23.not_rightInverseUniqueConjecture
#print axioms NLA.IE23.euclideanNorm
#assert_trust kernel NLA.IE23.euclideanNorm
#print axioms NLA.IE23.lpNorm
#assert_trust kernel NLA.IE23.lpNorm
#print axioms NLA.IE23.ratioSet
#assert_trust kernel NLA.IE23.ratioSet
#print axioms NLA.IE23.inducedNorm
#assert_trust kernel NLA.IE23.inducedNorm
#print axioms NLA.IE23.FullRowRank
#assert_trust kernel NLA.IE23.FullRowRank
#print axioms NLA.IE23.moorePenrose
#assert_trust kernel NLA.IE23.moorePenrose
#print axioms NLA.IE23.IsRightInverse
#assert_trust kernel NLA.IE23.IsRightInverse
#print axioms NLA.IE23.IsNormMinimizer
#assert_trust kernel NLA.IE23.IsNormMinimizer
#print axioms NLA.IE23.rightInverseNorms
#assert_trust kernel NLA.IE23.rightInverseNorms
#print axioms NLA.IE23.RightInverseUniqueConjecture
#assert_trust kernel NLA.IE23.RightInverseUniqueConjecture
#print axioms NLA.IE23.witnessA
#assert_trust kernel NLA.IE23.witnessA
#print axioms NLA.IE23.witnessGram
#assert_trust kernel NLA.IE23.witnessGram
#print axioms NLA.IE23.witnessGramInv
#assert_trust kernel NLA.IE23.witnessGramInv
#print axioms NLA.IE23.witnessB
#assert_trust kernel NLA.IE23.witnessB
#print axioms NLA.IE23.witnessX
#assert_trust kernel NLA.IE23.witnessX
#print axioms NLA.IE23.normingVector
#assert_trust kernel NLA.IE23.normingVector
#print axioms NLA.IE23.witnessNorm
#assert_trust kernel NLA.IE23.witnessNorm
