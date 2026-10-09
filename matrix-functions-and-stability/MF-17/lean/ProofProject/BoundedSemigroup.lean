import ProofProject.OscillatorySemigroup

/-!
# The uniformly bounded semigroups used in the oscillatory argument

This is a proof-side bundle. The stable semigroup in the target retains its
original exponential bound. The source rescaling supplies the bounded bundle
with exactly the same constant.
-/

noncomputable section

namespace ProofProject

universe u

structure BoundedSemigroup (M : ℝ) (H : Type u) [NormedAddCommGroup H]
    [NormedSpace ℂ H] where
  op : ℝ → H →L[ℂ] H
  at_zero : op 0 = ContinuousLinearMap.id ℂ H
  add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → op (s + t) = (op s).comp (op t)
  strong_continuous : ∀ x : H, ContinuousOn (fun t : ℝ => op t x) (Set.Ici 0)
  bound : ∀ t : ℝ, 0 ≤ t → ‖op t‖ ≤ M

namespace BoundedSemigroup

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
lemma bound_nonneg (S : BoundedSemigroup M H) : 0 ≤ M :=
  (norm_nonneg (S.op 0)).trans (S.bound 0 le_rfl)

theorem adjoint_strong_continuous (S : BoundedSemigroup M H) (x : H) :
    ContinuousOn (fun t : ℝ => star (S.op t) x) (Set.Ici 0) :=
  boundedSemigroup_adjoint_strong_continuous S.op S.at_zero S.add S.strong_continuous S.bound x

/-- The adjoint bundle uses no additional continuity assumption. -/
def adjoint (S : BoundedSemigroup M H) : BoundedSemigroup M H where
  op t := star (S.op t)
  at_zero := by simp only [S.at_zero, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id]
  add s t hs ht := by
    rw [add_comm s t, S.add t s ht hs]
    simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp]
  strong_continuous := S.adjoint_strong_continuous
  bound t ht := by simpa only [norm_star] using S.bound t ht

@[simp]
lemma adjoint_op (S : BoundedSemigroup M H) (t : ℝ) :
    S.adjoint.op t = star (S.op t) := rfl

/-- The exact bounded semigroup appearing after the source's time change. -/
def ofStableRescale (T : StableSemigroup M H) (t : ℝ) (ht : 0 < t) :
    BoundedSemigroup M H where
  op := T.oscillatoryRescale t
  at_zero := T.oscillatoryRescale_zero t
  add _ _ hu hv := T.oscillatoryRescale_add ht hu hv
  strong_continuous := T.oscillatoryRescale_strong_continuous ht
  bound _ hu := T.norm_oscillatoryRescale_le ht hu

@[simp]
lemma ofStableRescale_op (T : StableSemigroup M H) (t : ℝ) (ht : 0 < t) (s : ℝ) :
    (ofStableRescale T t ht).op s = (Real.exp (s / t) : ℂ) • T.op (s / t) := rfl

end BoundedSemigroup

end ProofProject
