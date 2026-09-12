/- Independent root inspection of the actual statement environment; no proof is implemented. -/
import NLA.MI22.Definitions
import LeanCert.Tactic.Verification

set_option pp.explicit true
set_option leancert.trust "kernel"

#print NLA.MI22.spectralPower
#assert_trust kernel NLA.MI22.spectralPower
#print axioms NLA.MI22.spectralPower

#print NLA.MI22.weightedMean
#assert_trust kernel NLA.MI22.weightedMean
#print axioms NLA.MI22.weightedMean

#print NLA.MI22.leftProduct
#assert_trust kernel NLA.MI22.leftProduct
#print axioms NLA.MI22.leftProduct

#print NLA.MI22.singularValue
#assert_trust kernel NLA.MI22.singularValue
#print axioms NLA.MI22.singularValue

#print NLA.MI22.singularPrefix
#assert_trust kernel NLA.MI22.singularPrefix
#print axioms NLA.MI22.singularPrefix

#print NLA.MI22.SingularLogMajorized
#assert_trust kernel NLA.MI22.SingularLogMajorized
#print axioms NLA.MI22.SingularLogMajorized

#print NLA.MI22.WeightedLogMajorizationConjecture
#assert_trust kernel NLA.MI22.WeightedLogMajorizationConjecture
#print axioms NLA.MI22.WeightedLogMajorizationConjecture

#print NLA.MI22.operatorNorm
#assert_trust kernel NLA.MI22.operatorNorm
#print axioms NLA.MI22.operatorNorm

#print NLA.MI22.frobeniusSquared
#assert_trust kernel NLA.MI22.frobeniusSquared
#print axioms NLA.MI22.frobeniusSquared

#print NLA.MI22.witnessD
#assert_trust kernel NLA.MI22.witnessD
#print axioms NLA.MI22.witnessD

#print NLA.MI22.witnessDInv
#assert_trust kernel NLA.MI22.witnessDInv
#print axioms NLA.MI22.witnessDInv

#print NLA.MI22.witnessA
#assert_trust kernel NLA.MI22.witnessA
#print axioms NLA.MI22.witnessA

#print NLA.MI22.witnessT
#assert_trust kernel NLA.MI22.witnessT
#print axioms NLA.MI22.witnessT

#print NLA.MI22.witnessLDL
#assert_trust kernel NLA.MI22.witnessLDL
#print axioms NLA.MI22.witnessLDL

#print NLA.MI22.witnessPivots
#assert_trust kernel NLA.MI22.witnessPivots
#print axioms NLA.MI22.witnessPivots

#print NLA.MI22.witnessB
#assert_trust kernel NLA.MI22.witnessB
#print axioms NLA.MI22.witnessB

#print NLA.MI22.witnessAOneEighth
#assert_trust kernel NLA.MI22.witnessAOneEighth
#print axioms NLA.MI22.witnessAOneEighth

#print NLA.MI22.witnessAFiveEighths
#assert_trust kernel NLA.MI22.witnessAFiveEighths
#print axioms NLA.MI22.witnessAFiveEighths

#print NLA.MI22.witnessRoot
#assert_trust kernel NLA.MI22.witnessRoot
#print axioms NLA.MI22.witnessRoot

#print NLA.MI22.witnessN
#assert_trust kernel NLA.MI22.witnessN
#print axioms NLA.MI22.witnessN

#print NLA.MI22.witnessVector
#assert_trust kernel NLA.MI22.witnessVector
#print axioms NLA.MI22.witnessVector

#print NLA.MI22.witnessTestValue
#assert_trust kernel NLA.MI22.witnessTestValue
#print axioms NLA.MI22.witnessTestValue

#check LinearMap.singularValues_fin
#check LinearMap.singularValues_antitone
#check LinearMap.singularValues_of_finrank_le
#check Matrix.toEuclideanCLM
