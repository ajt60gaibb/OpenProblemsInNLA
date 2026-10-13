import NLA.Proofs.MF03.FiniteElementaryLimit

/-!
Fixed-size determinant limits from the reviewed finite elementary-coefficient
limits. Tableau identities and determinant positivity remain separate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Filter

namespace NLA.Proofs.MF03

/-- The exact finite rectangular elementary-coefficient determinant. -/
noncomputable def finiteCosineRectDet (N m : ℕ) : ℝ :=
  Matrix.det (fun r c : Fin m =>
    finiteCosineElementaryCoeff N (m + c.val - r.val))

/-- The finite augmented determinant shifts exactly the first j rows. -/
noncomputable def finiteCosineAugDet (N m j : ℕ) : ℝ :=
  Matrix.det (fun r c : Fin m =>
    finiteCosineElementaryCoeff N
      (m + (if r.val < j then 1 else 0) + c.val - r.val))

/-- The original infinite rectangular determinant in the all-order contract. -/
noncomputable def cosineRectDet (m : ℕ) : ℝ :=
  Matrix.det (fun r c : Fin m =>
    cosineElementaryCoeff (m + c.val - r.val))

/-- The original infinite augmented determinant in the all-order contract. -/
noncomputable def cosineAugDet (m j : ℕ) : ℝ :=
  Matrix.det (fun r c : Fin m =>
    cosineElementaryCoeff
      (m + (if r.val < j then 1 else 0) + c.val - r.val))

/-- A zero bottom-row length gives the rectangle, at every finite cutoff. -/
theorem finiteCosineAugDet_zero (N m : ℕ) :
    finiteCosineAugDet N m 0 = finiteCosineRectDet N m := by
  simp [finiteCosineAugDet, finiteCosineRectDet]

/-- A zero bottom-row length gives the original infinite rectangle. -/
theorem cosineAugDet_zero (m : ℕ) :
    cosineAugDet m 0 = cosineRectDet m := by
  simp [cosineAugDet, cosineRectDet]

private theorem det_tendsto_of_entrywise (m : ℕ)
    (A : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ)
    (h : ∀ r c : Fin m, Tendsto (fun N => A N r c) atTop (nhds (B r c))) :
    Tendsto (fun N => (A N).det) atTop (nhds B.det) := by
  have hA : Tendsto A atTop (nhds B) := by
    apply tendsto_pi_nhds.mpr
    intro r
    apply tendsto_pi_nhds.mpr
    intro c
    exact h r c
  exact (continuous_id.matrix_det.tendsto B).comp hA

/-- The finite rectangular determinant converges to the exact original one. -/
theorem finiteCosineRectDet_tendsto (m : ℕ) :
    Tendsto (fun N : ℕ => finiteCosineRectDet N m)
      atTop (nhds (cosineRectDet m)) := by
  apply det_tendsto_of_entrywise m
    (fun N r c => finiteCosineElementaryCoeff N (m + c.val - r.val))
    (fun r c => cosineElementaryCoeff (m + c.val - r.val))
  intro r c
  exact finiteCosineElementaryCoeff_tendsto _

/-- The finite augmented determinant converges with the exact row shift. -/
theorem finiteCosineAugDet_tendsto (m j : ℕ) (_hj : j ≤ m) :
    Tendsto (fun N : ℕ => finiteCosineAugDet N m j)
      atTop (nhds (cosineAugDet m j)) := by
  apply det_tendsto_of_entrywise m
    (fun N r c => finiteCosineElementaryCoeff N
      (m + (if r.val < j then 1 else 0) + c.val - r.val))
    (fun r c => cosineElementaryCoeff
      (m + (if r.val < j then 1 else 0) + c.val - r.val))
  intro r c
  exact finiteCosineElementaryCoeff_tendsto _

#assert_trust kernel finiteCosineAugDet_zero
#assert_trust kernel cosineAugDet_zero
#assert_trust kernel finiteCosineRectDet_tendsto
#assert_trust kernel finiteCosineAugDet_tendsto

end NLA.Proofs.MF03
