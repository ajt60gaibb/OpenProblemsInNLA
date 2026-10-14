import NLA.Proofs.MF03.FiniteBidiagonalStep

/-!
Finite minor Cauchy–Binet for the exact MF-03 path-chain bridge. This file is
developed in stages; no determinant/tableau identity is assumed.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

private abbrev Site (m : ℕ) := Fin (2 * m + 1)

noncomputable instance strictRows_fintype (m : ℕ) : Fintype (StrictRows m) :=
  by
    classical
    unfold StrictRows
    infer_instance

/-- Expand a product minor over all intermediate tuples before sorting them. -/
theorem finiteMinor_mul_expand_allMaps (m : ℕ)
    (A C : Matrix (Site m) (Site m) ℝ)
    (X Z : Fin m → Site m) :
    Matrix.det (Matrix.submatrix (A * C) X Z) =
      ∑ f : Fin m → Site m,
        Matrix.det (Matrix.submatrix A X f) *
          ∏ p : Fin m, C (f p) (Z p) := by
  calc
    Matrix.det (Matrix.submatrix (A * C) X Z) =
        ∑ f : Fin m → Site m,
          ∑ σ : Equiv.Perm (Fin m),
            ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ p : Fin m,
              A (X (σ p)) (f p) * C (f p) (Z p) := by
                simp only [Matrix.det_apply', Matrix.submatrix_apply,
                  Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum,
                  Fintype.piFinset_univ]
                rw [Finset.sum_comm]
    _ = ∑ f : Fin m → Site m,
          Matrix.det (Matrix.submatrix A X f) *
            ∏ p : Fin m, C (f p) (Z p) := by
              apply Finset.sum_congr rfl
              intro f hf
              rw [Matrix.det_apply']
              simp only [Matrix.submatrix_apply, Finset.sum_mul,
                ← Finset.prod_mul_distrib, mul_assoc]

private theorem finiteMinor_det_zero_of_noninjective (m : ℕ)
    (A : Matrix (Site m) (Site m) ℝ)
    (X : Fin m → Site m) (f : Fin m → Site m)
    (hf : ¬ Function.Injective f) :
    Matrix.det (Matrix.submatrix A X f) = 0 := by
  simp only [Function.Injective, not_forall] at hf
  obtain ⟨p, q, hpq, hne⟩ := hf
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp [Matrix.submatrix_apply, hpq]

/-- The all-map expansion only receives contributions from injective tuples. -/
theorem finiteMinor_mul_expand_injective (m : ℕ)
    (A C : Matrix (Site m) (Site m) ℝ)
    (X Z : Fin m → Site m) :
    Matrix.det (Matrix.submatrix (A * C) X Z) =
      ∑ f : {f : Fin m → Site m // Function.Injective f},
        Matrix.det (Matrix.submatrix A X f.1) *
          ∏ p : Fin m, C (f.1 p) (Z p) := by
  classical
  rw [finiteMinor_mul_expand_allMaps]
  have hfilter :
      (∑ f : Fin m → Site m,
        Matrix.det (Matrix.submatrix A X f) *
          ∏ p : Fin m, C (f p) (Z p)) =
      ∑ f ∈ (Finset.univ.filter Function.Injective),
        Matrix.det (Matrix.submatrix A X f) *
          ∏ p : Fin m, C (f p) (Z p) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro f hf hnot
    have hni : ¬ Function.Injective f := by simpa using hnot
    rw [finiteMinor_det_zero_of_noninjective m A X f hni]
    simp
  rw [hfilter]
  simpa using (Finset.sum_subtype_eq_sum_filter
    (s := (Finset.univ : Finset (Fin m → Site m)))
    (p := Function.Injective)
    (f := fun f => Matrix.det (Matrix.submatrix A X f) *
      ∏ p : Fin m, C (f p) (Z p))).symm

private def sortedRows (m : ℕ) (f : Fin m → Site m)
    (hf : Function.Injective f) : StrictRows m :=
  ⟨f ∘ Tuple.sort f,
    (Tuple.monotone_sort f).strictMono_of_injective
      (hf.comp (Tuple.sort f).injective)⟩

private def injectiveTupleToPair (m : ℕ)
    (f : {f : Fin m → Site m // Function.Injective f}) :
    StrictRows m × Equiv.Perm (Fin m) :=
  (sortedRows m f.1 f.2, (Tuple.sort f.1)⁻¹)

private def pairToInjectiveTuple (m : ℕ)
    (pair : StrictRows m × Equiv.Perm (Fin m)) :
    {f : Fin m → Site m // Function.Injective f} :=
  ⟨pair.1.1 ∘ pair.2, pair.1.2.injective.comp pair.2.injective⟩

private def injectiveTupleEquivPair (m : ℕ) :
    {f : Fin m → Site m // Function.Injective f} ≃
      StrictRows m × Equiv.Perm (Fin m) where
  toFun := injectiveTupleToPair m
  invFun := pairToInjectiveTuple m
  left_inv := by
    intro f
    apply Subtype.ext
    funext p
    simp [injectiveTupleToPair, pairToInjectiveTuple, sortedRows,
      Function.comp_def]
  right_inv := by
    intro pair
    rcases pair with ⟨Y, σ⟩
    let f : Fin m → Site m := Y.1 ∘ σ
    have hfinj : Function.Injective f := Y.2.injective.comp σ.injective
    have hmono : Monotone (f ∘ (σ⁻¹ : Equiv.Perm (Fin m))) := by
      simpa [f, Function.comp_def] using Y.2.monotone
    have hfun : f ∘ Tuple.sort f = f ∘ (σ⁻¹ : Equiv.Perm (Fin m)) :=
      Tuple.unique_monotone (Tuple.monotone_sort f) hmono
    have hsort : Tuple.sort f = σ⁻¹ := by
      apply Equiv.ext
      intro p
      exact hfinj (congrFun hfun p)
    apply Prod.ext
    · apply Subtype.ext
      funext p
      change Y.1 (σ (Tuple.sort f p)) = Y.1 p
      rw [hsort]
      simp
    · change (Tuple.sort f)⁻¹ = σ
      rw [hsort]
      simp

/-- Finite minor Cauchy–Binet, with one sorted map per intermediate subset. -/
theorem finiteMinor_cauchyBinet (m : ℕ)
    (A C : Matrix (Site m) (Site m) ℝ) (X Z : StrictRows m) :
    Matrix.det (Matrix.submatrix (A * C) X.1 Z.1) =
      ∑ Y : StrictRows m,
        Matrix.det (Matrix.submatrix A X.1 Y.1) *
          Matrix.det (Matrix.submatrix C Y.1 Z.1) := by
  classical
  rw [finiteMinor_mul_expand_injective]
  calc
    (∑ f : {f : Fin m → Site m // Function.Injective f},
        Matrix.det (Matrix.submatrix A X.1 f.1) *
          ∏ p : Fin m, C (f.1 p) (Z.1 p)) =
      ∑ pair : StrictRows m × Equiv.Perm (Fin m),
        Matrix.det (Matrix.submatrix A X.1 (pair.1.1 ∘ pair.2)) *
          ∏ p : Fin m, C (pair.1.1 (pair.2 p)) (Z.1 p) := by
            apply Fintype.sum_equiv (injectiveTupleEquivPair m)
            intro f
            have hf := congrArg Subtype.val ((injectiveTupleEquivPair m).left_inv f)
            have hmap :
                ((injectiveTupleEquivPair m) f).1.1 ∘
                  ((injectiveTupleEquivPair m) f).2 = f.1 := by
              simpa [injectiveTupleEquivPair, pairToInjectiveTuple] using hf
            change
              Matrix.det (Matrix.submatrix A X.1 f.1) *
                  (∏ p : Fin m, C (f.1 p) (Z.1 p)) =
                Matrix.det (Matrix.submatrix A X.1
                  (((injectiveTupleEquivPair m) f).1.1 ∘
                    ((injectiveTupleEquivPair m) f).2)) *
                  (∏ p : Fin m,
                    C ((((injectiveTupleEquivPair m) f).1.1 ∘
                      ((injectiveTupleEquivPair m) f).2) p) (Z.1 p))
            rw [hmap]
    _ = ∑ Y : StrictRows m,
          ∑ σ : Equiv.Perm (Fin m),
            Matrix.det (Matrix.submatrix A X.1 (Y.1 ∘ σ)) *
              ∏ p : Fin m, C (Y.1 (σ p)) (Z.1 p) := by
                simp only [Fintype.sum_prod_type]
    _ = ∑ Y : StrictRows m,
          Matrix.det (Matrix.submatrix A X.1 Y.1) *
            Matrix.det (Matrix.submatrix C Y.1 Z.1) := by
              apply Finset.sum_congr rfl
              intro Y hY
              have hperm (σ : Equiv.Perm (Fin m)) :
                  Matrix.det (Matrix.submatrix A X.1 (Y.1 ∘ σ)) =
                    ((Equiv.Perm.sign σ : ℤ) : ℝ) *
                      Matrix.det (Matrix.submatrix A X.1 Y.1) := by
                simpa [Matrix.submatrix_submatrix, Function.comp_def] using
                  (Matrix.det_permute' σ (Matrix.submatrix A X.1 Y.1))
              have hdetC :
                  (∑ σ : Equiv.Perm (Fin m),
                    ((Equiv.Perm.sign σ : ℤ) : ℝ) *
                      ∏ p : Fin m, C (Y.1 (σ p)) (Z.1 p)) =
                    Matrix.det (Matrix.submatrix C Y.1 Z.1) := by
                rw [Matrix.det_apply']
                rfl
              simp_rw [hperm]
              calc
                (∑ σ : Equiv.Perm (Fin m),
                    (((Equiv.Perm.sign σ : ℤ) : ℝ) *
                      Matrix.det (Matrix.submatrix A X.1 Y.1)) *
                    ∏ p : Fin m, C (Y.1 (σ p)) (Z.1 p)) =
                  Matrix.det (Matrix.submatrix A X.1 Y.1) *
                    ∑ σ : Equiv.Perm (Fin m),
                      ((Equiv.Perm.sign σ : ℤ) : ℝ) *
                        ∏ p : Fin m, C (Y.1 (σ p)) (Z.1 p) := by
                          rw [Finset.mul_sum]
                          apply Finset.sum_congr rfl
                          intro σ hσ
                          ring
                _ = _ := by rw [hdetC]

#assert_trust kernel finiteMinor_mul_expand_allMaps
#assert_trust kernel finiteMinor_mul_expand_injective
#assert_trust kernel finiteMinor_cauchyBinet
#print axioms finiteMinor_cauchyBinet

end NLA.Proofs.MF03
