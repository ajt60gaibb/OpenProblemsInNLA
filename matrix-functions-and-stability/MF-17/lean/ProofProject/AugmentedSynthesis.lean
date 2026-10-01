import ProofProject.RoundedSpace

/-!
# The augmented Hilbert family for approximate synthesis

Adjoin weighted Euclidean coordinates to a finite family in `H`. Its exact
energy identity allows approximate tail separation in `H` to become an exact
tail bound in a genuine Hilbert space. Zero weights and zero vectors are
allowed throughout the main construction and bound.
-/

noncomputable section

namespace ProofProject

universe u

abbrev AugmentedSpace (H : Type u) (n : ℕ) :=
  WithLp 2 (H × EuclideanSpace ℂ (Fin n))

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

/-- The auxiliary coordinate energy, with possibly zero real weights. -/
def augmentedCoefficientEnergy (w : Fin n → ℝ) (c : Fin n → ℂ) : ℝ :=
  ∑ j, ‖c j‖ ^ 2 * w j ^ 2

lemma augmentedCoefficientEnergy_nonneg (w : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤ augmentedCoefficientEnergy w c :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

def augmentedWeightedCoordinates (w : Fin n → ℝ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun c j := (w j : ℂ) * c j
  map_add' c d := by ext j; simp [mul_add]
  map_smul' a c := by ext j; simp [mul_left_comm]

/-- Synthesis together with the independently recorded Euclidean coordinates. -/
def augmentedEmbedding (y : Fin n → H) (w : Fin n → ℝ) :
    (Fin n → ℂ) →ₗ[ℂ] AugmentedSpace H n :=
  (WithLp.linearEquiv 2 ℂ (H × EuclideanSpace ℂ (Fin n))).symm.toLinearMap.comp
    ((finiteSynthesisLinear y).prod
      ((EuclideanSpace.equiv (Fin n) ℂ).symm.toLinearMap.comp (augmentedWeightedCoordinates w)))

@[simp]
lemma augmentedEmbedding_fst (y : Fin n → H) (w : Fin n → ℝ) (c : Fin n → ℂ) :
    (augmentedEmbedding y w c).fst = finiteSynthesis y c := rfl

@[simp]
lemma augmentedEmbedding_snd (y : Fin n → H) (w : Fin n → ℝ) (c : Fin n → ℂ) :
    (augmentedEmbedding y w c).snd =
      (EuclideanSpace.equiv (Fin n) ℂ).symm (fun j => (w j : ℂ) * c j) := rfl

lemma augmentedEmbedding_snd_norm_sq (y : Fin n → H) (w : Fin n → ℝ) (c : Fin n → ℂ) :
    ‖(augmentedEmbedding y w c).snd‖ ^ 2 = augmentedCoefficientEnergy w c := by
  rw [augmentedEmbedding_snd, EuclideanSpace.norm_sq_eq]
  change (∑ j, ‖(w j : ℂ) * c j‖ ^ 2) = augmentedCoefficientEnergy w c
  simp only [augmentedCoefficientEnergy, norm_mul,
    mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma augmentedEmbedding_norm_sq (y : Fin n → H) (w : Fin n → ℝ) (c : Fin n → ℂ) :
    ‖augmentedEmbedding y w c‖ ^ 2 =
      ‖finiteSynthesis y c‖ ^ 2 + augmentedCoefficientEnergy w c := by
  rw [WithLp.prod_norm_sq_eq_of_L2, augmentedEmbedding_fst, augmentedEmbedding_snd_norm_sq]

/-- The augmented vectors are the images of the ordinary coordinate vectors. -/
def augmentedFamily (y : Fin n → H) (w : Fin n → ℝ) (j : Fin n) : AugmentedSpace H n :=
  augmentedEmbedding y w (Pi.single j 1)

@[simp]
lemma augmentedFamily_fst (y : Fin n → H) (w : Fin n → ℝ) (j : Fin n) :
    (augmentedFamily y w j).fst = y j := by
  simp [augmentedFamily, finiteSynthesis, Pi.single_apply]

lemma augmentedFamily_synthesis (y : Fin n → H) (w : Fin n → ℝ) (c : Fin n → ℂ) :
    finiteSynthesis (augmentedFamily y w) c = augmentedEmbedding y w c := by
  have hc : (∑ j : Fin n, c j • (Pi.single j (1 : ℂ) : Fin n → ℂ)) = c := by
    ext i
    simp [Pi.single_apply]
  conv_rhs => rw [← hc]
  rw [map_sum]
  simp only [finiteSynthesis, map_smul, augmentedFamily]

/-- Each augmented vector has the source's exact squared norm. -/
theorem augmentedFamily_norm_sq (y : Fin n → H) (w : Fin n → ℝ) (j : Fin n) :
    ‖augmentedFamily y w j‖ ^ 2 = ‖y j‖ ^ 2 + w j ^ 2 := by
  rw [augmentedFamily, augmentedEmbedding_norm_sq]
  simp [finiteSynthesis, augmentedCoefficientEnergy, Pi.single_apply, apply_ite, ite_mul]

/-- Exact augmented synthesis energy, with no nonzero-input assumption. -/
theorem augmentedFamily_synthesis_norm_sq (y : Fin n → H) (w : Fin n → ℝ) (c : Fin n → ℂ) :
    ‖finiteSynthesis (augmentedFamily y w) c‖ ^ 2 =
      ‖finiteSynthesis y c‖ ^ 2 + augmentedCoefficientEnergy w c := by
  rw [augmentedFamily_synthesis, augmentedEmbedding_norm_sq]

lemma augmentedFamily_tail (y : Fin n → H) (w : Fin n → ℝ) (c : Fin n → ℂ) (k : ℕ) :
    synthesisTail (augmentedFamily y w) c k =
      augmentedEmbedding y w (fun j => if k ≤ j.val then c j else 0) := by
  rw [← augmentedFamily_synthesis]
  simp only [synthesisTail, finiteSynthesis, ite_smul, zero_smul]

lemma augmentedEmbedding_tail_fst (y : Fin n → H) (w : Fin n → ℝ)
    (c : Fin n → ℂ) (k : ℕ) :
    (augmentedEmbedding y w (fun j => if k ≤ j.val then c j else 0)).fst =
      synthesisTail y c k := by
  rw [augmentedEmbedding_fst]
  simp only [finiteSynthesis, synthesisTail, ite_smul, zero_smul]

lemma augmentedEmbedding_tail_snd_norm_le (y : Fin n → H) (w : Fin n → ℝ)
    (c : Fin n → ℂ) (k : ℕ) :
    ‖(augmentedEmbedding y w (fun j => if k ≤ j.val then c j else 0)).snd‖ ≤
      ‖(augmentedEmbedding y w c).snd‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [augmentedEmbedding_snd_norm_sq, augmentedEmbedding_snd_norm_sq]
  apply Finset.sum_le_sum
  intro j hj
  by_cases h : k ≤ j.val
  · simp [h]
  · simp only [h, ite_false, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The Euclidean coordinate term is controlled by the full augmented norm. -/
lemma augmentedCoefficientEnergy_sqrt_le (y : Fin n → H) (w : Fin n → ℝ) (c : Fin n → ℂ) :
    Real.sqrt (augmentedCoefficientEnergy w c) ≤ ‖augmentedEmbedding y w c‖ := by
  rw [← augmentedEmbedding_snd_norm_sq y w c, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact WithLp.norm_snd_le H (augmentedEmbedding y w c)

/-- Approximate separation in the original space gives an exact coefficient
 tail bound in the augmented Hilbert space. The hypothesis `M≥1` is essential
 for controlling the auxiliary Euclidean tail by the same constant. -/
theorem augmentedFamily_tail_bound (y : Fin n → H) (w : Fin n → ℝ)
    {M ε : ℝ} (hM : 1 ≤ M) (hε : 0 ≤ ε) (R : H →L[ℂ] H) (hR : ‖R‖ ≤ M)
    (c : Fin n → ℂ) (k : ℕ)
    (herr : ‖synthesisTail y c k - R (finiteSynthesis y c)‖ ≤
      ε * Real.sqrt (augmentedCoefficientEnergy w c)) :
    ‖synthesisTail (augmentedFamily y w) c k‖ ≤
      (M + ε) * ‖finiteSynthesis (augmentedFamily y w) c‖ := by
  let v := augmentedEmbedding y w c
  let t := augmentedEmbedding y w (fun j => if k ≤ j.val then c j else 0)
  let q : AugmentedSpace H n := WithLp.toLp 2 (R v.fst, t.snd)
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hM
  have hM2 : 1 ≤ M ^ 2 := by nlinarith
  have hs : ‖t.snd‖ ≤ ‖v.snd‖ := augmentedEmbedding_tail_snd_norm_le y w c k
  have hr : ‖R v.fst‖ ≤ M * ‖v.fst‖ :=
    (R.le_opNorm _).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  have hq : ‖q‖ ≤ M * ‖v‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM0 (norm_nonneg _))).mp
    rw [mul_pow, WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    change ‖R v.fst‖ ^ 2 + ‖t.snd‖ ^ 2 ≤ M ^ 2 * (‖v.fst‖ ^ 2 + ‖v.snd‖ ^ 2)
    have hr2 := pow_le_pow_left₀ (norm_nonneg _) hr 2
    have hs2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
    have hscale : ‖v.snd‖ ^ 2 ≤ M ^ 2 * ‖v.snd‖ ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) hM2
    nlinarith
  have hdiff : ‖t - q‖ = ‖t.fst - R v.fst‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖t.fst - R v.fst‖ ^ 2 + ‖t.snd - t.snd‖ ^ 2 = ‖t.fst - R v.fst‖ ^ 2
    simp
  have herror : ‖t - q‖ ≤ ε * Real.sqrt (augmentedCoefficientEnergy w c) := by
    rw [hdiff]
    change ‖(augmentedEmbedding y w (fun j => if k ≤ j.val then c j else 0)).fst -
      R ((augmentedEmbedding y w c).fst)‖ ≤ _
    rw [augmentedEmbedding_tail_fst, augmentedEmbedding_fst]
    exact herr
  rw [augmentedFamily_tail, augmentedFamily_synthesis]
  change ‖t‖ ≤ (M + ε) * ‖v‖
  have htriangle : ‖t‖ ≤ ‖q‖ + ‖t - q‖ := by
    convert norm_add_le q (t - q) using 1 <;> abel
  calc
    ‖t‖ ≤ ‖q‖ + ‖t - q‖ := htriangle
    _ ≤ M * ‖v‖ + ε * Real.sqrt (augmentedCoefficientEnergy w c) := add_le_add hq herror
    _ ≤ M * ‖v‖ + ε * ‖v‖ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (augmentedCoefficientEnergy_sqrt_le y w c) hε)
    _ = (M + ε) * ‖v‖ := by ring

end ProofProject
