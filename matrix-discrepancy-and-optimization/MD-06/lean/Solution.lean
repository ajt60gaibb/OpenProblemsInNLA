import «Definitions»

namespace MD06

set_option autoImplicit false

variable (S : Semantics)

/-- The strong event exposes the nonsynchronized critical point required by the
paper theorem.  This is a definitional projection only; no analytic claim is
silently substituted for the missing Hessian-to-local-minimum argument. -/
theorem stable_event_has_nonsync_critical (n : Nat) (G : S.Graph n)
    (h : hasStableNonsynchronizedCritical S G) :
    ∃ θ, S.critical G θ ∧ ¬ S.synchronized G θ := by
  rcases h with ⟨_, θ, hcrit, hnsync, _, _⟩
  exact ⟨θ, hcrit, hnsync⟩

#print axioms stable_event_has_nonsync_critical

end MD06
