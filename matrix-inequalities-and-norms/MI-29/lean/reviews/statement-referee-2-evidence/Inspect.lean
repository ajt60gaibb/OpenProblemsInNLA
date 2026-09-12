/- Independent statement inspection only: no mathematical proof implementation. -/
import Challenge

set_option pp.all true in
#print NLA.MI29.spectralPower
set_option pp.all true in
#print NLA.MI29.matrixModulus
set_option pp.all true in
#print NLA.MI29.ModulusDeterminantConjecture
set_option pp.all true in
#print NLA.MI29.spectralPower_natCast
#print NLA.MI29.modulus_power_eight
#print NLA.MI29.comparison_positive_real
#print NLA.MI29.counterexample
#print NLA.MI29.not_modulusDeterminantConjecture
#check CFC.rpow_eq_cfc_real
#check CFC.rpow_zero
#check CFC.rpow_natCast
#check CFC.abs_sq
#check CFC.abs_nonneg
#check Matrix.nonneg_iff_posSemidef
#check Matrix.isStrictlyPositive_iff_posDef
#check IsStrictlyPositive.rpow
#check Matrix.PosDef.det_pos
#check Complex.le_def
#check Complex.lt_def
#print axioms NLA.MI29.spectralPower
#print axioms NLA.MI29.matrixModulus
#print axioms NLA.MI29.ModulusDeterminantConjecture
