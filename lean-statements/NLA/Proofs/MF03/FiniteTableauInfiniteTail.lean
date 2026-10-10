import NLA.Proofs.MF03.FiniteTableauTailBound

/-!
The exact finite cosine-factor tail is bounded by its infinite counterpart.
This retains the zero-based label start `m` and remains a tableau-sum gate;
the determinant/tableau bridge is separate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

private theorem cosineFactor_pos_all (k : ℕ) :
    0 < cosineFactor (k + 1) := by
  unfold cosineFactor
  have hk : (0 : ℝ) < (((k + 1 : ℕ) : ℝ) - 1 / 2) := by
    have hnonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    push_cast
    linarith
  positivity

private theorem cosineFactors_summable_all :
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

private theorem cosineTail_summable_all (m : ℕ) :
    Summable (fun t : ℕ => cosineFactor (m + t + 1)) := by
  have h := cosineFactors_summable_all.comp_injective
    (show Function.Injective (fun t : ℕ => m + t) by
      intro a b h
      exact Nat.add_left_cancel h)
  simpa only [Function.comp_def] using h

/-- Exact finite tail over `m ≤ k < N` is no larger than the whole tail. -/
theorem finiteCosineTail_le_cosineTail (N m : ℕ) :
    finiteCosineTail N m ≤ cosineTail m := by
  let e : FiniteTailLabel N m → ℕ := fun k => k.val.val - m
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    apply Fin.ext
    dsimp [e] at hab
    have ha := a.2
    have hb := b.2
    omega
  have hfinite : Summable (fun k : FiniteTailLabel N m =>
      cosineFactor (k.val.val + 1)) := Summable.of_finite
  have hbound :
      (∑' k : FiniteTailLabel N m, cosineFactor (k.val.val + 1)) ≤
        ∑' t : ℕ, cosineFactor (m + t + 1) := by
    apply hfinite.tsum_le_tsum_of_inj e he
    · intro t ht
      exact (cosineFactor_pos_all (m + t)).le
    · intro k
      have hk : m ≤ k.val.val := k.2
      have hi : m + (k.val.val - m) = k.val.val := Nat.add_sub_of_le hk
      dsimp [e]
      rw [hi]
    · exact cosineTail_summable_all m
  simpa [finiteCosineTail, cosineTail] using hbound

private theorem finiteRectTableauSum_nonneg_all (N m : ℕ) :
    0 ≤ finiteRectTableauSum N m := by
  unfold finiteRectTableauSum finiteRectWeight
  apply Finset.sum_nonneg
  intro T hT
  apply Finset.prod_nonneg
  intro r hr
  apply Finset.prod_nonneg
  intro c hc
  exact (cosineFactor_pos_all (T.1 r c)).le

/-- The reviewed finite weighted-tableau bound with the fixed infinite tail. -/
theorem finiteAugTableauSum_le_rect_mul_cosineTail
    (N m j : ℕ) (hj : j ≤ m) :
    finiteAugTableauSum N m j ≤
      finiteRectTableauSum N m * (cosineTail m) ^ j := by
  calc
    finiteAugTableauSum N m j ≤
        finiteRectTableauSum N m * (finiteCosineTail N m) ^ j :=
      finiteAugTableauSum_le_rect_mul_tail N m j hj
    _ ≤ finiteRectTableauSum N m * (cosineTail m) ^ j := by
      apply mul_le_mul_of_nonneg_left _ (finiteRectTableauSum_nonneg_all N m)
      exact pow_le_pow_left₀ (by
        unfold finiteCosineTail
        exact Finset.sum_nonneg (fun k hk => (cosineFactor_pos_all k.val.val).le))
        (finiteCosineTail_le_cosineTail N m) _

#assert_trust kernel finiteCosineTail_le_cosineTail
#assert_trust kernel finiteAugTableauSum_le_rect_mul_cosineTail

end NLA.Proofs.MF03
