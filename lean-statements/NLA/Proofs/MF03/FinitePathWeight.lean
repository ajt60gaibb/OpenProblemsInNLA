import NLA.Proofs.MF03.FinitePathLabels

/-!
The exact product weight of a finite valid MF-03 path chain, expressed by
its zero-based advance labels. No tableau bijection is assumed.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

private theorem finiteValidStep_entry (m k : ℕ) (X Y : StrictRows m)
    (hv : finiteValidStep m X Y) (p : Fin m) :
    finiteBidiagonal m k (X.1 p) (Y.1 p) =
      if (Y.1 p).val = (X.1 p).val + 1 then
        cosineFactor (k + 1) else 1 := by
  change (if (Y.1 p).val = (X.1 p).val then (1 : ℝ)
    else if (Y.1 p).val = (X.1 p).val + 1 then
      cosineFactor (k + 1) else 0) = _
  by_cases hadvance : (Y.1 p).val = (X.1 p).val + 1
  · simp [hadvance]
  · have hstay := (hv p).resolve_right hadvance
    simp [hstay]

/-- A path-chain weight is exactly the product of cosine factors indexed by
the advance labels in each column. -/
theorem finiteValidPathWeight_eq_labelProducts (m : ℕ) :
    ∀ (N : ℕ) (X Z : StrictRows m)
      (c : FiniteValidPath m N X Z),
      finiteValidPathWeight m N X Z c =
        ∏ p : Fin m,
          ∏ k ∈ finiteAdvanceLabels m N X Z c p,
            cosineFactor (k + 1) := by
  intro N
  induction N with
  | zero =>
      intro X Z c
      simp [finiteValidPathWeight, finiteAdvanceLabels]
  | succ N ih =>
      intro X Z c
      rcases c with ⟨Y, ⟨hvalid, tail⟩⟩
      have hstep : finiteStepWeight m N X Y =
          ∏ p : Fin m,
            if (Y.1 p).val = (X.1 p).val + 1 then
              cosineFactor (N + 1) else 1 := by
        unfold finiteStepWeight
        apply Finset.prod_congr rfl
        intro p hp
        exact finiteValidStep_entry m N X Y hvalid.down p
      change finiteStepWeight m N X Y *
        finiteValidPathWeight m N Y Z tail = _
      rw [hstep, ih Y Z tail, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      by_cases hadvance : (Y.1 p).val = (X.1 p).val + 1
      · have hfresh : N ∉ finiteAdvanceLabels m N Y Z tail p := by
          intro hN
          have hlt := finiteAdvanceLabels_lt m N Y Z tail p N hN
          omega
        simp [finiteAdvanceLabels, hadvance,
          Finset.prod_insert hfresh]
      · simp [finiteAdvanceLabels, hadvance]

#assert_trust kernel finiteValidPathWeight_eq_labelProducts
#print axioms finiteValidPathWeight_eq_labelProducts

end NLA.Proofs.MF03
