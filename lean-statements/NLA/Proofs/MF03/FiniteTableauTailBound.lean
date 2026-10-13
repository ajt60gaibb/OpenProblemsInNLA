import NLA.Proofs.MF03.FiniteTableauWeightFactor

/-!
The reviewed finite-tableau upper bound by the exact zero-based cosine tail.
This is a finite sum theorem; the dual Jacobi--Trudi determinant identity and
the infinite determinant limit are separate gates.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- A bounded factor label in the tail starting at the zero-based index `m`. -/
def FiniteTailLabel (N m : ℕ) : Type :=
  {k : Fin N // m ≤ k.val}

noncomputable instance finiteTailLabel_fintype (N m : ℕ) :
    Fintype (FiniteTailLabel N m) := by
  classical
  unfold FiniteTailLabel
  infer_instance

/-- Exact finite tail `Σ_{m≤k<N} a_k`, with `a_k=cosineFactor(k+1)`. -/
noncomputable def finiteCosineTail (N m : ℕ) : ℝ :=
  ∑ k : FiniteTailLabel N m, cosineFactor (k.val.val + 1)

private def tableauTailTuple (N m j : ℕ) (hj : j ≤ m)
    (T : FiniteTableau (finiteAugShape m j) N) :
    Fin j → FiniteTailLabel N m :=
  fun c => ⟨finiteBottomTuple N m j hj T c,
    finiteAugTableau_bottom_ge N m j hj T c⟩

private def tableauTailPair (N m j : ℕ) (hj : j ≤ m)
    (T : FiniteTableau (finiteAugShape m j) N) :
    FiniteTableau (finiteRectShape m) N × (Fin j → FiniteTailLabel N m) :=
  (finiteRectRestrict N m j T, tableauTailTuple N m j hj T)

private theorem tableauTailPair_injective (N m j : ℕ) (hj : j ≤ m) :
    Function.Injective (tableauTailPair N m j hj) := by
  intro T U hpair
  apply finiteTableauRestrictPair_injective N m j hj
  apply Prod.ext
  · simpa [tableauTailPair, finiteTableauRestrictPair] using
      congrArg Prod.fst hpair
  · funext c
    exact congrArg Subtype.val (congrFun (congrArg Prod.snd hpair) c)

private theorem cosineFactor_tail_pos (k : ℕ) :
    0 < cosineFactor (k + 1) := by
  unfold cosineFactor
  have hk : (0 : ℝ) < (((k + 1 : ℕ) : ℝ) - 1 / 2) := by
    have hnonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    push_cast
    linarith
  positivity

private theorem finiteRectWeight_nonneg (m : ℕ) (T : ℕ → ℕ → ℕ) :
    0 ≤ finiteRectWeight m T := by
  unfold finiteRectWeight
  apply Finset.prod_nonneg
  intro r hr
  apply Finset.prod_nonneg
  intro c hc
  exact (cosineFactor_tail_pos (T r c)).le

private theorem tailTupleWeight_nonneg (N m j : ℕ)
    (b : Fin j → FiniteTailLabel N m) :
    0 ≤ ∏ c : Fin j, cosineFactor ((b c).val.val + 1) := by
  apply Finset.prod_nonneg
  intro c hc
  exact (cosineFactor_tail_pos ((b c).val.val)).le

/-- The exact finite augmented-tableau weighted sum is bounded by the
rectangular sum times the `j`-fold zero-based factor tail. -/
theorem finiteAugTableauSum_le_rect_mul_tail (N m j : ℕ) (hj : j ≤ m) :
    finiteAugTableauSum N m j ≤
      finiteRectTableauSum N m * (finiteCosineTail N m) ^ j := by
  classical
  let A := FiniteTableau (finiteAugShape m j) N
  let R := FiniteTableau (finiteRectShape m) N
  let B := Fin j → FiniteTailLabel N m
  let φ : A → R × B := tableauTailPair N m j hj
  let w : R × B → ℝ := fun p =>
    finiteRectWeight m p.1.1 *
      ∏ c : Fin j, cosineFactor ((p.2 c).val.val + 1)
  have hφ : Function.Injective φ := tableauTailPair_injective N m j hj
  have hw (p : R × B) : 0 ≤ w p := by
    exact mul_nonneg (finiteRectWeight_nonneg m p.1.1)
      (tailTupleWeight_nonneg N m j p.2)
  have hfactor (T : A) :
      finiteRectWeight m T.1 * finiteBottomWeight j m T.1 = w (φ T) := by
    simpa [w, φ, tableauTailPair, tableauTailTuple,
      finiteBottomTupleWeight, finiteTableauRestrictPair]
      using finiteAugTableau_weight_factor N m j hj T
  let S : Finset (R × B) := Finset.univ.image φ
  have himage : (∑ T : A, w (φ T)) = ∑ p ∈ S, w p := by
    simp only [S]
    exact (Finset.sum_image (s := Finset.univ) (f := w) (g := φ)
      (by intro x hx y hy h; exact hφ h)).symm
  have hsub : (∑ p ∈ S, w p) ≤ ∑ p : R × B, w p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.subset_univ _
    · intro p hp hnot
      exact hw p
  calc
    finiteAugTableauSum N m j = ∑ T : A, w (φ T) := by
      unfold finiteAugTableauSum
      apply Finset.sum_congr rfl
      intro T hT
      exact hfactor T
    _ = ∑ p ∈ S, w p := himage
    _ ≤ ∑ p : R × B, w p := hsub
    _ = finiteRectTableauSum N m * (finiteCosineTail N m) ^ j := by
      simp only [w, Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      change (∑ T : FiniteTableau (finiteRectShape m) N,
          finiteRectWeight m T.1) *
        (∑ b : Fin j → FiniteTailLabel N m,
          ∏ c : Fin j, cosineFactor ((b c).val.val + 1)) =
        finiteRectTableauSum N m * (finiteCosineTail N m) ^ j
      rw [← Fintype.sum_pow
        (fun k : FiniteTailLabel N m => cosineFactor (k.val.val + 1)) j]
      rfl

#assert_trust kernel finiteAugTableauSum_le_rect_mul_tail
#print axioms finiteAugTableauSum_le_rect_mul_tail

end NLA.Proofs.MF03
