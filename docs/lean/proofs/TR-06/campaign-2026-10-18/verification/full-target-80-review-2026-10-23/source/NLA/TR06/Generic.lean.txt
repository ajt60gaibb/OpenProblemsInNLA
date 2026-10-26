/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.Definitions
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.TR06

/-- A principal exceptional set suffices because a witness outside a family
of polynomial zero sets already violates one equation in that family. -/
theorem generic_iff_source (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    GenericComplexIdentifiable d n r ↔ SourceGenericComplexIdentifiable d n r := by
  constructor
  · rintro ⟨p, hproper, hgeneric⟩
    refine ⟨{p}, ?_, ?_⟩
    · rcases hproper with ⟨A, hA, hpA⟩
      exact ⟨A, hA, p, Set.mem_singleton p, hpA⟩
    · intro A hA hpA
      rcases hpA with ⟨q, hq, hqA⟩
      have hqp : q = p := Set.mem_singleton_iff.mp hq
      subst q
      exact hgeneric A hA hqA
  · rintro ⟨P, ⟨A, hA, p, hp, hpA⟩, hgeneric⟩
    refine ⟨p, ⟨A, hA, hpA⟩, ?_⟩
    intro B hB hpB
    exact hgeneric B hB ⟨p, hp, hpB⟩

#print axioms generic_iff_source
#assert_trust kernel generic_iff_source
end NLA.TR06
