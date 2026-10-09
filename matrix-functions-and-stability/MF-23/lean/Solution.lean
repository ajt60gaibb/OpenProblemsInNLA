import CanonicalBridge

/-!
The proved export selected by Comparator. Its exact type is duplicated in
`Challenge`, while its proof imports the immutable upstream direct proof and
the independently reviewed block-order bridge.
-/

set_option autoImplicit false

namespace NLA.MF23

theorem canonical_crouzeix : Target := by
  exact canonical_crouzeix_proved

end NLA.MF23
