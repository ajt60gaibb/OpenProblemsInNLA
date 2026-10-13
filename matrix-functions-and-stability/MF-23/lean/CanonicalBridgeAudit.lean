import CanonicalBridge
import LeanCert.Tactic.Verification

set_option leancert.trust "kernel"

#assert_trust kernel OAI.DirectCrouzeix.complete_crouzeix
#assert_trust kernel NLA.MF23.canonical_crouzeix_proved

#print axioms OAI.DirectCrouzeix.complete_crouzeix
#print axioms NLA.MF23.canonical_crouzeix_proved
