import NLA.Proofs.MF03.CosineCoefficientTransfer

/-!
Finite elementary coefficients for the exact cosine-product factors and their
limit to the existing infinite cardinality-subtype coefficient.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Filter

namespace NLA.Proofs.MF03

/-- The exact elementary coefficient from subsets of the first N factors. -/
noncomputable def finiteCosineElementaryCoeff (N j : ℕ) : ℝ :=
  ∑ S ∈ (Finset.range N).powersetCard j,
    ∏ k ∈ S, cosineFactor (k + 1)

private theorem finiteElementary_factor_pos (k : ℕ) :
    0 < cosineFactor (k + 1) := by
  unfold cosineFactor
  have hk : (0 : ℝ) < (((k + 1 : ℕ) : ℝ) - 1 / 2) := by
    have hnonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    push_cast
    linarith
  positivity

private theorem finiteElementary_factor_summable :
    Summable (fun k : ℕ => cosineFactor (k + 1)) := by
  have hbase : Summable (fun k : ℕ =>
      1 / |(k : ℝ) + 1 / 2| ^ (2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow (1 / 2) 2).2 (by norm_num)
  have hbase' : Summable (fun k : ℕ =>
      1 / |(k : ℝ) + 1 / 2| ^ (2 : ℕ)) := by
    simpa only [Real.rpow_two] using hbase
  have hscale := hbase'.mul_left (1 / Real.pi ^ 2)
  apply hscale.congr
  intro k
  have hcast : (((k + 1 : ℕ) : ℝ) - 1 / 2) = (k : ℝ) + 1 / 2 := by
    push_cast
    ring
  have hpos : (0 : ℝ) < (k : ℝ) + 1 / 2 := by positivity
  have hfactor : cosineFactor (k + 1) =
      1 / (Real.pi ^ 2 * ((k : ℝ) + 1 / 2) ^ 2) := by
    unfold cosineFactor
    rw [hcast]
  rw [hfactor, abs_of_pos hpos, one_div_mul_one_div]

private noncomputable def finiteElementaryWeight (S : Finset ℕ) : ℝ :=
  ∏ k ∈ S, cosineFactor (k + 1)

private theorem finiteElementaryWeight_nonneg (S : Finset ℕ) :
    0 ≤ finiteElementaryWeight S := by
  exact Finset.prod_nonneg (fun k hk => (finiteElementary_factor_pos k).le)

private theorem finiteElementaryWeight_summable :
    Summable finiteElementaryWeight := by
  apply summable_finsetProd_of_summable_norm
  simpa [finiteElementaryWeight, Real.norm_eq_abs,
    abs_of_pos, finiteElementary_factor_pos] using
    finiteElementary_factor_summable

private noncomputable def finiteElementarySelected (j : ℕ) (S : Finset ℕ) : ℝ :=
  if S.card = j then finiteElementaryWeight S else 0

private theorem finiteElementarySelected_nonneg (j : ℕ) (S : Finset ℕ) :
    0 ≤ finiteElementarySelected j S := by
  by_cases h : S.card = j
  · simp [finiteElementarySelected, h, finiteElementaryWeight_nonneg]
  · simp [finiteElementarySelected, h]

private theorem finiteElementarySelected_summable (j : ℕ) :
    Summable (finiteElementarySelected j) := by
  apply Summable.of_nonneg_of_le
    (finiteElementarySelected_nonneg j)
    (fun S => by
      by_cases h : S.card = j
      · simp [finiteElementarySelected, h]
      · simpa [finiteElementarySelected, h] using
          finiteElementaryWeight_nonneg S)
    finiteElementaryWeight_summable

private theorem finiteElementary_sum_powerset (N j : ℕ) :
    finiteCosineElementaryCoeff N j =
      ∑ S ∈ (Finset.range N).powerset,
        finiteElementarySelected j S := by
  unfold finiteCosineElementaryCoeff
  rw [Finset.powersetCard_eq_filter]
  simp [Finset.sum_filter, finiteElementarySelected,
    finiteElementaryWeight]

private theorem finiteElementary_tsum_selected (j : ℕ) :
    (∑' S : Finset ℕ, finiteElementarySelected j S) =
      cosineElementaryCoeff j := by
  let s : Set (Finset ℕ) := {S | S.card = j}
  have hindicator (S : Finset ℕ) :
      finiteElementarySelected j S =
        Set.indicator s finiteElementaryWeight S := by
    by_cases h : S.card = j <;>
      simp [finiteElementarySelected, s, h, Set.indicator]
  simp_rw [hindicator]
  rw [← tsum_subtype s finiteElementaryWeight]
  rfl

/-- The finite elementary coefficient has only nonnegative summands. -/
theorem finiteCosineElementaryCoeff_nonneg (N j : ℕ) :
    0 ≤ finiteCosineElementaryCoeff N j := by
  unfold finiteCosineElementaryCoeff
  exact Finset.sum_nonneg (fun S hS => finiteElementaryWeight_nonneg S)

/-- Adding one factor cannot decrease an elementary coefficient. -/
theorem finiteCosineElementaryCoeff_mono (N j : ℕ) :
    finiteCosineElementaryCoeff N j ≤
      finiteCosineElementaryCoeff (N + 1) j := by
  unfold finiteCosineElementaryCoeff
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro S hS
    have h := Finset.mem_powersetCard.mp hS
    exact Finset.mem_powersetCard.mpr
      ⟨h.1.trans (Finset.range_mono (Nat.le_succ N)), h.2⟩
  · intro S hS hnot
    exact finiteElementaryWeight_nonneg S

/-- Each finite cutoff is bounded by the original infinite coefficient. -/
theorem finiteCosineElementaryCoeff_le (N j : ℕ) :
    finiteCosineElementaryCoeff N j ≤ cosineElementaryCoeff j := by
  rw [finiteElementary_sum_powerset,
    ← finiteElementary_tsum_selected j]
  exact (finiteElementarySelected_summable j).sum_le_tsum
    ((Finset.range N).powerset)
    (fun S hS => finiteElementarySelected_nonneg j S)

/-- The nested finite coefficients converge to the exact original tsum. -/
theorem finiteCosineElementaryCoeff_tendsto (j : ℕ) :
    Tendsto (fun N : ℕ => finiteCosineElementaryCoeff N j)
      atTop (nhds (cosineElementaryCoeff j)) := by
  have hcutoff : Tendsto (fun N : ℕ => (Finset.range N).powerset)
      atTop atTop :=
    tendsto_finset_powerset_atTop_atTop.comp tendsto_finset_range
  have h := (finiteElementarySelected_summable j).hasSum.comp hcutoff
  change Tendsto
    (fun N : ℕ => ∑ S ∈ (Finset.range N).powerset,
      finiteElementarySelected j S) atTop
    (nhds (∑' S : Finset ℕ, finiteElementarySelected j S)) at h
  have hEq :
      (fun N : ℕ => ∑ S ∈ (Finset.range N).powerset,
        finiteElementarySelected j S) =
      (fun N : ℕ => finiteCosineElementaryCoeff N j) := by
    funext N
    exact (finiteElementary_sum_powerset N j).symm
  rw [hEq, finiteElementary_tsum_selected] at h
  exact h

#assert_trust kernel finiteCosineElementaryCoeff_nonneg
#assert_trust kernel finiteCosineElementaryCoeff_mono
#assert_trust kernel finiteCosineElementaryCoeff_le
#assert_trust kernel finiteCosineElementaryCoeff_tendsto

end NLA.Proofs.MF03
