import Solution

/- Inspect the actual retained checker term and its final consumers. This is
an implementation audit, not an additional assumed certificate. -/
set_option pp.proofs true in
#print NLA.MI22.numerical_separation

set_option pp.proofs true in
#print NLA.MI22.counterexample_proved

set_option pp.proofs true in
#print NLA.MI22.not_weightedLogMajorizationConjecture_proved
