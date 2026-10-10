import NLA.Proofs.MF03.FiniteMinorCauchyBinet

/-!
The finite path-chain expansion of the exact MF-03 bidiagonal product minor.
The factor at the first transition of a length `N + 1` chain is `B_N`.
The endpoint tableau bijection remains a separate obligation.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

private noncomputable instance (m : ℕ) : DecidableEq (StrictRows m) :=
  Classical.decEq _

/-- Dynamic sum over all ordered intermediate positions. Invalid transitions
have zero `finiteStepWeight`, so this is the weighted valid-chain sum. -/
noncomputable def finiteChainSum (m : ℕ) :
    (N : ℕ) → StrictRows m → StrictRows m → ℝ
  | 0, X, Z => if X = Z then 1 else 0
  | N + 1, X, Z =>
      ∑ Y : StrictRows m,
        finiteStepWeight m N X Y * finiteChainSum m N Y Z

private theorem finiteOneMinor_perm_eq_id (m : ℕ)
    (X Z : StrictRows m) (σ : Equiv.Perm (Fin m))
    (hprod : (∏ p : Fin m,
      (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ)
        (X.1 (σ p)) (Z.1 p)) ≠ 0) :
    σ = 1 ∧ X = Z := by
  have hterm (p : Fin m) : X.1 (σ p) = Z.1 p := by
    have hp := (Finset.prod_ne_zero_iff.mp hprod) p (Finset.mem_univ p)
    by_contra hne
    exact hp (Matrix.one_apply_ne hne)
  have hmono : StrictMono (σ : Fin m → Fin m) := by
    intro p q hpq
    by_contra hnot
    have hneq : σ p ≠ σ q := by
      intro heq
      exact (ne_of_lt hpq) (σ.injective heq)
    have hrev : σ q < σ p := by omega
    have hx := X.2 hrev
    have hz := Z.2 hpq
    rw [hterm q, hterm p] at hx
    exact (not_lt_of_ge (le_of_lt hz)) hx
  have hs : σ = 1 := by
    apply Equiv.ext
    intro p
    simpa using congrFun hmono.eq_id p
  constructor
  · exact hs
  · apply Subtype.ext
    funext p
    simpa [hs] using hterm p

private theorem finiteOneMinor_det (m : ℕ) (X Z : StrictRows m) :
    Matrix.det (Matrix.submatrix
      (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ)
      X.1 Z.1) = if X = Z then 1 else 0 := by
  classical
  by_cases h : X = Z
  · subst Z
    simp [Matrix.submatrix_one X.1 X.2.injective]
  · rw [Matrix.det_apply']
    have hs (σ : Equiv.Perm (Fin m)) :
        (∏ p : Fin m,
          (Matrix.submatrix
            (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ)
            X.1 Z.1) (σ p) p) = 0 := by
      by_contra hp
      have heq := (finiteOneMinor_perm_eq_id m X Z σ (by
        simpa [Matrix.submatrix_apply] using hp)).2
      exact h heq
    simp only [Matrix.submatrix_apply] at hs
    simp [hs, h]

/-- Exact finite Cauchy–Binet expansion into ordered bidiagonal chains,
uniformly in the path count and number of cosine factors. -/
theorem finiteProduct_minor_eq_chainSum (m N : ℕ) (X Z : StrictRows m) :
    Matrix.det (Matrix.submatrix (finiteBidiagonalProduct m N)
      X.1 Z.1) = finiteChainSum m N X Z := by
  induction N generalizing X Z with
  | zero =>
      simpa [finiteBidiagonalProduct, finiteChainSum] using
        finiteOneMinor_det m X Z
  | succ N ih =>
      change Matrix.det (Matrix.submatrix
        (finiteBidiagonal m N * finiteBidiagonalProduct m N)
        X.1 Z.1) = finiteChainSum m (N + 1) X Z
      rw [finiteMinor_cauchyBinet]
      simp_rw [finiteBidiagonal_minor_eq_step, ih]
      rfl

/-- A geometric one-factor move: each path stays or advances one site. -/
def finiteValidStep (m : ℕ) (X Y : StrictRows m) : Prop :=
  ∀ p : Fin m,
    (Y.1 p).val = (X.1 p).val ∨
      (Y.1 p).val = (X.1 p).val + 1

private theorem finiteStepWeight_zero_of_invalid (m k : ℕ)
    (X Y : StrictRows m) (h : ¬ finiteValidStep m X Y) :
    finiteStepWeight m k X Y = 0 := by
  by_contra hw
  have hterm (p : Fin m) :
      finiteBidiagonal m k (X.1 p) (Y.1 p) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp (by
      simpa [finiteStepWeight] using hw)) p (Finset.mem_univ p)
  apply h
  intro p
  have hp := hterm p
  unfold finiteBidiagonal at hp
  split_ifs at hp with hdiag hstep
  · exact Or.inl hdiag
  · exact Or.inr hstep
  · exact False.elim (hp rfl)

/-- Actual finite chains of valid ordered position maps. The recursive
constructor records the first intermediate map, then the remaining chain. -/
def FiniteValidPath (m : ℕ) :
    (N : ℕ) → StrictRows m → StrictRows m → Type
  | 0, X, Z => PLift (X = Z)
  | N + 1, X, Z =>
      Σ Y : StrictRows m,
        PLift (finiteValidStep m X Y) × FiniteValidPath m N Y Z

@[instance_reducible] private noncomputable def finiteValidPathFintype (m : ℕ) :
    (N : ℕ) → (X Z : StrictRows m) → Fintype (FiniteValidPath m N X Z)
  | 0, X, Z => by
      classical
      change Fintype (PLift (X = Z))
      infer_instance
  | N + 1, X, Z => by
      classical
      letI : ∀ Y : StrictRows m,
          Fintype (FiniteValidPath m N Y Z) :=
        fun Y => finiteValidPathFintype m N Y Z
      change Fintype (Σ Y : StrictRows m,
        PLift (finiteValidStep m X Y) × FiniteValidPath m N Y Z)
      infer_instance

noncomputable instance finiteValidPath_fintype (m N : ℕ)
    (X Z : StrictRows m) : Fintype (FiniteValidPath m N X Z) :=
  finiteValidPathFintype m N X Z

/-- The weight of a valid chain, with descending factor labels. -/
noncomputable def finiteValidPathWeight (m : ℕ) :
    (N : ℕ) → (X Z : StrictRows m) → FiniteValidPath m N X Z → ℝ
  | 0, _, _, _ => 1
  | N + 1, X, Z, ⟨Y, ⟨_, c⟩⟩ =>
      finiteStepWeight m N X Y * finiteValidPathWeight m N Y Z c

/-- Literal sum over all geometrically valid chains. -/
noncomputable def finiteValidPathSum (m N : ℕ) (X Z : StrictRows m) : ℝ :=
  ∑ c : FiniteValidPath m N X Z,
    finiteValidPathWeight m N X Z c

private theorem finiteValidPathSum_zero (m : ℕ) (X Z : StrictRows m) :
    finiteValidPathSum m 0 X Z = if X = Z then 1 else 0 := by
  classical
  by_cases h : X = Z
  · subst Z
    letI : Unique (FiniteValidPath m 0 X X) :=
      { default := ⟨rfl⟩, uniq := by intro c; cases c; rfl }
    simp [finiteValidPathSum, finiteValidPathWeight]
  · letI : IsEmpty (FiniteValidPath m 0 X Z) :=
      ⟨fun c => h c.down⟩
    simp [finiteValidPathSum, finiteValidPathWeight, h]

private theorem finiteValidPathSum_succ (m N : ℕ) (X Z : StrictRows m) :
    finiteValidPathSum m (N + 1) X Z =
      ∑ Y : StrictRows m,
        finiteStepWeight m N X Y * finiteValidPathSum m N Y Z := by
  classical
  -- Summation over the dependent first-step choice and the remaining chain.
  rw [finiteValidPathSum]
  change (∑ c : Σ Y : StrictRows m,
      PLift (finiteValidStep m X Y) × FiniteValidPath m N Y Z,
        finiteStepWeight m N X c.1 *
          finiteValidPathWeight m N c.1 Z c.2.2) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Y hY
  rw [Fintype.sum_prod_type]
  by_cases hv : finiteValidStep m X Y
  · letI : Unique (PLift (finiteValidStep m X Y)) :=
      { default := ⟨hv⟩, uniq := by intro a; cases a; rfl }
    simp [finiteValidPathSum]
    rw [Finset.mul_sum]
  · have hw := finiteStepWeight_zero_of_invalid m N X Y hv
    simp [finiteValidPathSum, hw, hv]

/-- The dynamic sum is exactly the sum over geometrically valid chains. -/
theorem finiteChainSum_eq_validPathSum (m N : ℕ) (X Z : StrictRows m) :
    finiteChainSum m N X Z = finiteValidPathSum m N X Z := by
  induction N generalizing X Z with
  | zero =>
      exact (finiteValidPathSum_zero m X Z).symm
  | succ N ih =>
      rw [finiteChainSum, finiteValidPathSum_succ]
      apply Finset.sum_congr rfl
      intro Y hY
      rw [ih]

/-- Exact product minor as the literal sum over all valid finite path chains. -/
theorem finiteProduct_minor_eq_validPathSum (m N : ℕ)
    (X Z : StrictRows m) :
    Matrix.det (Matrix.submatrix (finiteBidiagonalProduct m N)
      X.1 Z.1) = finiteValidPathSum m N X Z := by
  rw [finiteProduct_minor_eq_chainSum, finiteChainSum_eq_validPathSum]

#assert_trust kernel finiteProduct_minor_eq_chainSum
#print axioms finiteProduct_minor_eq_chainSum
#assert_trust kernel finiteProduct_minor_eq_validPathSum
#print axioms finiteProduct_minor_eq_validPathSum

end NLA.Proofs.MF03
