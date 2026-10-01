import ProofProject.BasisEnergy

/-!
# Mean and variance for replicated coefficients

The replicated metric is the sum of the mean-synthesis energy and the
within-group variance. The identities in this file isolate one copied group
without treating its mean and variance as independent errors.
-/

noncomputable section

open scoped BigOperators

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

/-- The average coefficient in one group of `r` copies. -/
def copiedMean (r : ℕ) (ξ : Fin n → Fin r → ℂ) (i : Fin n) : ℂ :=
  (r : ℂ)⁻¹ * ∑ l, ξ i l

/-- The unnormalized within-group variance. -/
def copiedVariance (r : ℕ) (ξ : Fin n → Fin r → ℂ) (i : Fin n) : ℝ :=
  ∑ l, ‖ξ i l - copiedMean r ξ i‖ ^ 2

/-- The coefficient energy in the replicated Hilbert model. -/
def copiedEnergy (f : Fin n → H) (r : ℕ) (ξ : Fin n → Fin r → ℂ) : ℝ :=
  (r : ℝ) * ‖finiteSynthesis f (copiedMean r ξ)‖ ^ 2 + ∑ i, copiedVariance r ξ i

lemma copiedVariance_nonneg (r : ℕ) (ξ : Fin n → Fin r → ℂ) (i : Fin n) :
    0 ≤ copiedVariance r ξ i :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma copiedEnergy_nonneg (f : Fin n → H) (r : ℕ) (ξ : Fin n → Fin r → ℂ) :
    0 ≤ copiedEnergy f r ξ := by
  unfold copiedEnergy
  exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (Finset.sum_nonneg fun i _ => copiedVariance_nonneg r ξ i)

lemma copiedMean_add (r : ℕ) (ξ ζ : Fin n → Fin r → ℂ) (i : Fin n) :
    copiedMean r (ξ + ζ) i = copiedMean r ξ i + copiedMean r ζ i := by
  simp [copiedMean, Finset.sum_add_distrib, mul_add]

lemma copiedMean_smul (r : ℕ) (a : ℂ) (ξ : Fin n → Fin r → ℂ) (i : Fin n) :
    copiedMean r (a • ξ) i = a * copiedMean r ξ i := by
  simp only [copiedMean, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

@[simp] lemma copiedMean_zero (r : ℕ) : copiedMean r (0 : Fin n → Fin r → ℂ) = 0 := by
  funext i
  simp [copiedMean]

lemma copiedMean_const {r : ℕ} (hr : 0 < r) (c : Fin n → ℂ) :
    copiedMean r (fun i _ => c i) = c := by
  have hrC : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  funext i
  simp [copiedMean, hrC]

lemma copiedMean_mul_card {r : ℕ} (hr : 0 < r) (ξ : Fin n → Fin r → ℂ) (i : Fin n) :
    (r : ℂ) * copiedMean r ξ i = ∑ l, ξ i l := by
  have hrC : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  simp [copiedMean, hrC]

lemma sum_copiedCentered {r : ℕ} (hr : 0 < r) (ξ : Fin n → Fin r → ℂ) (i : Fin n) :
    ∑ l, (ξ i l - copiedMean r ξ i) = 0 := by
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    copiedMean_mul_card hr, sub_self]

@[simp] lemma copiedVariance_const {r : ℕ} (hr : 0 < r) (c : Fin n → ℂ) (i : Fin n) :
    copiedVariance r (fun j _ => c j) i = 0 := by
  simp [copiedVariance, copiedMean_const hr c]

/-- Zero-mean perturbations add their squared norms without a cross term. -/
lemma sum_norm_sq_add_centered {ι : Type*} [Fintype ι] (v : H) (w : ι → H)
    (hw : ∑ l, w l = 0) :
    ∑ l, ‖v + w l‖ ^ 2 = (Fintype.card ι : ℝ) * ‖v‖ ^ 2 + ∑ l, ‖w l‖ ^ 2 := by
  have hcross : ∑ l, (inner ℂ v (w l)).re = 0 := by
    rw [← Complex.re_sum, ← inner_sum, hw]
    simp
  simp only [norm_add_sq (𝕜 := ℂ), Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  change (∑ l, RCLike.re (inner ℂ v (w l))) = 0 at hcross
  rw [hcross]
  ring

/-- The exact local mean/variance identity for a unit basis vector. -/
theorem copied_group_norm_sq_decomposition {r : ℕ} (hr : 0 < r)
    (ξ : Fin n → Fin r → ℂ) (i : Fin n) (v e : H) (he : ‖e‖ = 1) :
    ∑ l, ‖v + ξ i l • e‖ ^ 2 =
      (r : ℝ) * ‖v + copiedMean r ξ i • e‖ ^ 2 + copiedVariance r ξ i := by
  have hcenter : ∑ l, (ξ i l - copiedMean r ξ i) • e = 0 := by
    rw [← Finset.sum_smul, sum_copiedCentered hr ξ i]
    simp
  calc
    _ = ∑ l, ‖(v + copiedMean r ξ i • e) + (ξ i l - copiedMean r ξ i) • e‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro l _
      congr 2
      module
    _ = (r : ℝ) * ‖v + copiedMean r ξ i • e‖ ^ 2 +
        ∑ l, ‖(ξ i l - copiedMean r ξ i) • e‖ ^ 2 := by
      simpa using sum_norm_sq_add_centered (v + copiedMean r ξ i • e) _ hcenter
    _ = _ := by simp [copiedVariance, norm_smul, he]

/-- Scalar variance as the difference of the second moment and squared mean. -/
theorem copiedVariance_eq_sum_norm_sq_sub {r : ℕ} (hr : 0 < r)
    (ξ : Fin n → Fin r → ℂ) (i : Fin n) :
    copiedVariance r ξ i = (∑ l, ‖ξ i l‖ ^ 2) - (r : ℝ) * ‖copiedMean r ξ i‖ ^ 2 := by
  have h := copied_group_norm_sq_decomposition hr ξ i (0 : ℂ) 1 (by simp)
  simp only [smul_eq_mul, mul_one, zero_add] at h
  linarith

/-- Split the synthesis into one mean coordinate and all the others. -/
lemma finiteSynthesis_split_coordinate (f : Fin n → H) (c : Fin n → ℂ) (i : Fin n) :
    (∑ j, if j = i then 0 else c j • f j) + c i • f i = finiteSynthesis f c := by
  classical
  have hterm (j : Fin n) : c j • f j =
      (if j = i then 0 else c j • f j) + (if j = i then c i • f i else 0) := by
    by_cases hji : j = i <;> simp [hji]
  have hsum : (∑ j, c j • f j) = ∑ j,
      ((if j = i then 0 else c j • f j) + (if j = i then c i • f i else 0)) :=
    Finset.sum_congr rfl fun j _ => hterm j
  simpa [Finset.sum_add_distrib, finiteSynthesis] using hsum.symm

/-- The whole replicated energy decomposes into the exact local group
expression and the variances of all other groups. -/
theorem copiedEnergy_group_decomposition (f : Fin n → H) {r : ℕ} (hr : 0 < r)
    (ξ : Fin n → Fin r → ℂ) (i : Fin n) (hfi : ‖f i‖ = 1) :
    copiedEnergy f r ξ =
      (∑ l, ‖(∑ j, if j = i then 0 else copiedMean r ξ j • f j) + ξ i l • f i‖ ^ 2) +
      ∑ j, if j = i then 0 else copiedVariance r ξ j := by
  rw [copied_group_norm_sq_decomposition hr ξ i _ (f i) hfi,
    finiteSynthesis_split_coordinate]
  unfold copiedEnergy
  have hvar : copiedVariance r ξ i + (∑ j, if j = i then 0 else copiedVariance r ξ j) =
      ∑ j, copiedVariance r ξ j := by
    classical
    have hterm (j : Fin n) : copiedVariance r ξ j =
        (if j = i then copiedVariance r ξ i else 0) +
        (if j = i then 0 else copiedVariance r ξ j) := by
      by_cases hji : j = i <;> simp [hji]
    have hsum : (∑ j, copiedVariance r ξ j) = ∑ j,
        ((if j = i then copiedVariance r ξ i else 0) +
        (if j = i then 0 else copiedVariance r ξ j)) :=
      Finset.sum_congr rfl fun j _ => hterm j
    simpa [Finset.sum_add_distrib] using hsum.symm
  linarith

end ProofProject
