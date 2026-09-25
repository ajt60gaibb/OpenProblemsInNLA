import Mathlib
import Reduction

namespace IV02

set_option autoImplicit false

theorem rotation_identity_verified (P : PartitionData) (i : Fin P.m) :
    c P i ^ 2 + s P i ^ 2 = 1 :=
  rotation_identity P i

theorem layer_count_verified (P : PartitionData) :
    Even (layerCount P) ∧ 0 < layerCount P :=
  ⟨layerCount_even P, layerCount_pos P⟩

#print axioms rotation_identity_verified
#print axioms layer_count_verified

end IV02
