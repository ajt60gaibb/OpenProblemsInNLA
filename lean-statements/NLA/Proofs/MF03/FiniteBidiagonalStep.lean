import NLA.Proofs.MF03.FiniteBidiagonalMinor

/-!
The exact one-factor minor in the finite path-chain model. Cauchy–Binet,
chain sums, and the tableau bijection remain separate obligations.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- Strictly increasing positions for the `m` paths inside the `2m+1` sites. -/
def StrictRows (m : ℕ) :=
  {X : Fin m → Fin (2 * m + 1) // StrictMono X}

/-- The exact weight of one factor transition, zero if a path makes an invalid move. -/
noncomputable def finiteStepWeight (m k : ℕ) (X Y : StrictRows m) : ℝ :=
  ∏ p : Fin m, finiteBidiagonal m k (X.1 p) (Y.1 p)

private theorem finiteBidiagonal_nonzero_bounds (m k : ℕ)
    (i h : Fin (2 * m + 1)) (hne : finiteBidiagonal m k i h ≠ 0) :
    i.val ≤ h.val ∧ h.val ≤ i.val + 1 := by
  unfold finiteBidiagonal at hne
  split_ifs at hne with hdiag hstep
  · omega
  · omega
  · exact False.elim (hne rfl)

private theorem finiteBidiagonal_perm_eq_one (m k : ℕ)
    (X Y : StrictRows m) (σ : Equiv.Perm (Fin m))
    (hprod : (∏ p : Fin m,
      finiteBidiagonal m k (X.1 (σ p)) (Y.1 p)) ≠ 0) : σ = 1 := by
  have hterm (p : Fin m) :
      finiteBidiagonal m k (X.1 (σ p)) (Y.1 p) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod) p (Finset.mem_univ p)
  have hmono : StrictMono (σ : Fin m → Fin m) := by
    intro p q hpq
    by_contra hnot
    have hneq : σ p ≠ σ q := by
      intro heq
      have hpq' : p = q := σ.injective heq
      exact (ne_of_lt hpq) hpq'
    have hrev : σ q < σ p := by omega
    have hx : (X.1 (σ q)).val < (X.1 (σ p)).val := X.2 hrev
    have hy : (Y.1 p).val < (Y.1 q).val := Y.2 hpq
    have hp := finiteBidiagonal_nonzero_bounds m k _ _ (hterm p)
    have hq := finiteBidiagonal_nonzero_bounds m k _ _ (hterm q)
    omega
  apply Equiv.ext
  intro p
  have hp := congrFun hmono.eq_id p
  simpa using hp

/-- Every nonzero matching of an ordered bidiagonal minor is the identity. -/
theorem finiteBidiagonal_minor_eq_step (m k : ℕ) (X Y : StrictRows m) :
    Matrix.det (Matrix.submatrix (finiteBidiagonal m k) X.1 Y.1) =
      finiteStepWeight m k X Y := by
  classical
  rw [Matrix.det_apply']
  rw [Finset.sum_eq_single 1]
  · simp [finiteStepWeight]
  · intro σ hσ hne
    have hzero :
        (∏ p : Fin m,
          (Matrix.submatrix (finiteBidiagonal m k) X.1 Y.1) (σ p) p) = 0 := by
      by_contra hprod
      have hone : σ = 1 := finiteBidiagonal_perm_eq_one m k X Y σ (by
        simpa [Matrix.submatrix_apply] using hprod)
      exact hne hone
    simpa [Matrix.submatrix_apply] using hzero
  · simp

#assert_trust kernel finiteBidiagonal_minor_eq_step
#print axioms finiteBidiagonal_minor_eq_step

end NLA.Proofs.MF03
