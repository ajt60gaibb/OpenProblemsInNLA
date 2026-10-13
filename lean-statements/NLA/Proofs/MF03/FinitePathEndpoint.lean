import NLA.Proofs.MF03.FinitePathChain

/-!
The exact ordered endpoints of the finite MF-03 augmented minor. The
endpoint-to-tableau bijection is a separate obligation.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- Starting positions omit exactly row `j` among `0,...,m`. -/
def finitePathStart (m j : ℕ) (_hj : j ≤ m) : StrictRows m :=
  ⟨finiteMinorRow m j, by
    intro p q hpq
    apply Fin.lt_def.mpr
    simp only [finiteMinorRow]
    have hpqv : p.val < q.val := hpq
    split_ifs <;> omega⟩

/-- Terminal positions are `m+1,...,2m`. -/
def finitePathEnd (m : ℕ) : StrictRows m :=
  ⟨finiteMinorCol m, by
    intro p q hpq
    apply Fin.lt_def.mpr
    simp only [finiteMinorCol]
    omega⟩

/-- The original finite augmented determinant is the exact valid-chain sum
with its original row order, column order, and factor-label order. -/
theorem finiteCosineAugDet_eq_validPathSum (N m j : ℕ) (hj : j ≤ m) :
    finiteCosineAugDet N m j =
      finiteValidPathSum m N (finitePathStart m j hj) (finitePathEnd m) := by
  rw [finiteCosineAugDet_eq_bidiagonal_minor N m j hj]
  change Matrix.det (Matrix.submatrix (finiteBidiagonalProduct m N)
    (finitePathStart m j hj).1 (finitePathEnd m).1) = _
  exact finiteProduct_minor_eq_validPathSum m N
    (finitePathStart m j hj) (finitePathEnd m)

/-- Each path advances by the exact length of its augmented tableau column. -/
theorem finitePath_advance_count (m j : ℕ) (hj : j ≤ m) (p : Fin m) :
    ((finitePathEnd m).1 p).val -
      ((finitePathStart m j hj).1 p).val =
        if p.val < j then m + 1 else m := by
  simp only [finitePathStart, finitePathEnd,
    finiteMinorRow, finiteMinorCol]
  split_ifs <;> omega

#assert_trust kernel finiteCosineAugDet_eq_validPathSum
#assert_trust kernel finitePath_advance_count
#print axioms finiteCosineAugDet_eq_validPathSum
#print axioms finitePath_advance_count

end NLA.Proofs.MF03
