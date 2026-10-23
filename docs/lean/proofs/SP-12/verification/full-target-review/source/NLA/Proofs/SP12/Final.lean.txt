import NLA.Proofs.SP12.StrongDelta
import NLA.Proofs.SP12.VertexExtension
import NLA.Proofs.SP12.ChromaticInduction

/-! The complete, unchanged SP-12 target. Both constructive inputs to the
chromatic induction are supplied by the actual kernel-checked constructions. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP12

/-- Every positive-order finite simple graph has a positive semidefinite real
matrix with its exact off-diagonal pattern, the Strong Arnold property, and
nullity at least its chromatic number minus one. -/
theorem target : NLA.Statements.SP12.Target :=
  target_of_strongDelta_and_extension
    (fun _ G => exists_strongDelta_gram G)
    (fun _ _ G R hp hs => exists_vertexExtension G R hp hs)

#assert_trust kernel target
#print axioms target

end NLA.Proofs.SP12
