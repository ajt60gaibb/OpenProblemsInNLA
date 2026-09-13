/- Independent root inspection of actual statements. Shared printing/trust-command structure is reused; all mathematical meanings independently reviewed. -/
import NLA.IE23.Definitions
import LeanCert.Tactic.Verification

set_option leancert.trust "kernel"

#print NLA.IE23.Vec
#assert_trust kernel NLA.IE23.Vec
#print axioms NLA.IE23.Vec

#print NLA.IE23.Mat
#assert_trust kernel NLA.IE23.Mat
#print axioms NLA.IE23.Mat

#print NLA.IE23.euclideanNorm
#assert_trust kernel NLA.IE23.euclideanNorm
#print axioms NLA.IE23.euclideanNorm

#print NLA.IE23.lpNorm
#assert_trust kernel NLA.IE23.lpNorm
#print axioms NLA.IE23.lpNorm

#print NLA.IE23.ratioSet
#assert_trust kernel NLA.IE23.ratioSet
#print axioms NLA.IE23.ratioSet

#print NLA.IE23.inducedNorm
#assert_trust kernel NLA.IE23.inducedNorm
#print axioms NLA.IE23.inducedNorm

#print NLA.IE23.FullRowRank
#assert_trust kernel NLA.IE23.FullRowRank
#print axioms NLA.IE23.FullRowRank

#print NLA.IE23.moorePenrose
#assert_trust kernel NLA.IE23.moorePenrose
#print axioms NLA.IE23.moorePenrose

#print NLA.IE23.IsRightInverse
#assert_trust kernel NLA.IE23.IsRightInverse
#print axioms NLA.IE23.IsRightInverse

#print NLA.IE23.IsNormMinimizer
#assert_trust kernel NLA.IE23.IsNormMinimizer
#print axioms NLA.IE23.IsNormMinimizer

#print NLA.IE23.rightInverseNorms
#assert_trust kernel NLA.IE23.rightInverseNorms
#print axioms NLA.IE23.rightInverseNorms

#print NLA.IE23.RightInverseUniqueConjecture
#assert_trust kernel NLA.IE23.RightInverseUniqueConjecture
#print axioms NLA.IE23.RightInverseUniqueConjecture

#print NLA.IE23.witnessA
#assert_trust kernel NLA.IE23.witnessA
#print axioms NLA.IE23.witnessA

#print NLA.IE23.witnessGram
#assert_trust kernel NLA.IE23.witnessGram
#print axioms NLA.IE23.witnessGram

#print NLA.IE23.witnessGramInv
#assert_trust kernel NLA.IE23.witnessGramInv
#print axioms NLA.IE23.witnessGramInv

#print NLA.IE23.witnessB
#assert_trust kernel NLA.IE23.witnessB
#print axioms NLA.IE23.witnessB

#print NLA.IE23.witnessX
#assert_trust kernel NLA.IE23.witnessX
#print axioms NLA.IE23.witnessX

#print NLA.IE23.normingVector
#assert_trust kernel NLA.IE23.normingVector
#print axioms NLA.IE23.normingVector

#print NLA.IE23.witnessNorm
#assert_trust kernel NLA.IE23.witnessNorm
#print axioms NLA.IE23.witnessNorm

set_option pp.explicit true in
#print NLA.IE23.euclideanNorm

set_option pp.explicit true in
#print NLA.IE23.lpNorm

set_option pp.explicit true in
#print NLA.IE23.moorePenrose

#print Matrix.inv
#print Matrix.rank
#check EuclideanSpace.norm_sq_eq
#check isLUB_csSup

#print Matrix.toLin
#print Matrix.mulVec
#print NLA.IE23.ratioSet
#print NLA.IE23.rightInverseNorms
