import «Definitions»

namespace MD06

/-! Independent Challenge specification.

This file records the complete MD-06 contract.  It intentionally does not
supply an implementation of `Semantics`: the finite uniform measure, torus
local-minimum predicate, derivatives and the even-subsequence limit must be
constructed and proved from pinned analysis libraries. -/

variable (S : Semantics)

#check MainClaim S
#check StrongClaim S
#check everyLocalMinimumSynchronized
#check hasStableNonsynchronizedCritical

/-- Statement-level conjunction retaining both the negative limit and the
strong high-probability stable critical-point conclusion. -/
def CompleteTarget : Prop := MainClaim S ∧ StrongClaim S

theorem stable_event_has_nonsync_critical (n : Nat) (G : S.Graph n)
    (h : hasStableNonsynchronizedCritical S G) :
    ∃ θ, S.critical G θ ∧ ¬ S.synchronized G θ := by
  rcases h with ⟨_, θ, hcrit, hnsync, _, _⟩
  exact ⟨θ, hcrit, hnsync⟩

#check CompleteTarget S

end MD06
