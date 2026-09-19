import NLA.PF03.SeedLocalData0
import NLA.PF03.SeedLocalData1
import NLA.PF03.SeedLocalData2
import NLA.PF03.SeedLocalData3
import NLA.PF03.SeedLocalData4
import NLA.PF03.SeedLocalData5
import NLA.PF03.SeedLocalData6

/-!
C06: all internal finite certificates are actually discharged for all seven cones.
The exported statement is the unchanged frozen actual-cache/form/kernel/sign/minor
contract. Original seed mathematics: Sidney Holden, Flatiron Institute,
Simons Foundation. Formalization: George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology; Codex assistance.
-/
set_option autoImplicit false
open scoped BigOperators Matrix
noncomputable section
namespace NLA.PF03

theorem seed_local_data (i : Fin 7) :
    localCache i = localForm i ∧
      (localCache i).mulVec alphaVector = 0 ∧
      0 < localCache i 0 0 ∧
      0 < localCache i 0 0 * localCache i 1 1 - (localCache i 0 1) ^ 2 ∧
      seedMinor i ≠ 0 := by
  apply seed_local_data_of_certificate i
  fin_cases i
  · exact seed_local_rational_certificate0
  · exact seed_local_rational_certificate1
  · exact seed_local_rational_certificate2
  · exact seed_local_rational_certificate3
  · exact seed_local_rational_certificate4
  · exact seed_local_rational_certificate5
  · exact seed_local_rational_certificate6

#print axioms seed_local_data
#assert_trust kernel seed_local_data

end NLA.PF03
