import ProofProject.ReplicationDeficit
import ProofProject.BasisEnergy
import ProofProject.ReplicationOrder

/-!
# The deficit premise used by coefficient replication

The source's completed-square and boundary estimates provide inequalities for
every coefficient, so the replication theorem requires no infimum or minimizer.
-/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

/-- Synthesis with one coefficient removed. -/
def replicationBase (f : Fin n → H) (a : Fin n → ℂ) (i : Fin n) : H :=
  ∑ j, if j = i then 0 else a j • f j

/-- Synthesis of the groups strictly after the selected group. -/
def replicationTail (f : Fin n → H) (a : Fin n → ℂ) (i : Fin n) : H :=
  ∑ j, if i < j then a j • f j else 0

/-- The squared-norm deficit at one partially retained coefficient. -/
def coefficientDeficit (M : ℝ) (v y e : H) (t z : ℂ) : ℝ :=
  M ^ 2 * ‖v + t • e‖ ^ 2 - ‖y + (z * t) • e‖ ^ 2

/-- Uniform endpoint surplus and bounded intermediate deficit. The auxiliary
nonnegative quantity may depend on the other coefficients and the pivot. -/
def HasReplicationDeficits (f : Fin n → H) (M c C : ℝ) : Prop :=
  ∀ (a : Fin n → ℂ) (i : Fin n), ∃ h : ℝ, 0 ≤ h ∧
    (∀ t : ℂ, c * h ≤ coefficientDeficit M
      (replicationBase f a i) (replicationTail f a i) (f i) t 0) ∧
    (∀ t : ℂ, c * h ≤ coefficientDeficit M
      (replicationBase f a i) (replicationTail f a i) (f i) t 1) ∧
    (∀ t z : ℂ, ‖z‖ ≤ 1 → -C * h ≤ coefficientDeficit M
      (replicationBase f a i) (replicationTail f a i) (f i) t z)

/-- Replication absorbs one interior multiplier using all the endpoint copies. -/
theorem coefficientDeficit_sum_nonneg {r : ℕ} (pivot : Fin r)
    {M c C h : ℝ} (v y e : H) (t z : Fin r → ℂ)
    (hh : 0 ≤ h) (hbudget : C ≤ ((r : ℝ) - 1) * c)
    (hzero : ∀ t : ℂ, c * h ≤ coefficientDeficit M v y e t 0)
    (hone : ∀ t : ℂ, c * h ≤ coefficientDeficit M v y e t 1)
    (hinter : ∀ t z : ℂ, ‖z‖ ≤ 1 → -C * h ≤ coefficientDeficit M v y e t z)
    (hpivot : ‖z pivot‖ ≤ 1)
    (hother : ∀ l, l ≠ pivot → z l = 0 ∨ z l = 1) :
    ∑ l, ‖y + (z l * t l) • e‖ ^ 2 ≤ M ^ 2 * ∑ l, ‖v + t l • e‖ ^ 2 := by
  have hδ := replication_deficit_sum pivot
    (fun l => coefficientDeficit M v y e (t l) (z l)) hh hbudget
    (hinter _ _ hpivot) (by
      intro l hl
      rcases hother l hl with hz | hz
      · rw [hz]; exact hzero _
      · rw [hz]; exact hone _)
  simp only [coefficientDeficit, Finset.sum_sub_distrib, ← Finset.mul_sum] at hδ
  linarith

lemma replicationBase_copiedPattern (f : Fin n → H) {r : ℕ}
    (ξ : Fin n → Fin r → ℂ) (i : Fin n) (l : Fin r) (z : ℂ) :
    replicationBase f (copiedMean r (copiedPattern i l z ξ)) i =
      replicationTail f (copiedMean r ξ) i := by
  unfold replicationBase replicationTail
  apply Finset.sum_congr rfl
  intro j _
  rcases lt_trichotomy j i with hji | hji | hij
  · simp [hji.ne, hji.not_gt, copiedMean_pattern_of_lt i l z ξ hji]
  · subst j; simp
  · simp [hij.ne', hij, copiedMean_pattern_of_gt i l z ξ hij]

/-- Replication makes every elementary pattern bounded by exactly M in the
copied energy. The only input beyond unit vectors is the uniform deficit premise. -/
theorem copiedEnergy_pattern_bound (f : Fin n → H) {r : ℕ} (hr : 0 < r)
    {M c C : ℝ} (hM : 1 ≤ M) (hf : ∀ i, ‖f i‖ = 1)
    (hdef : HasReplicationDeficits f M c C) (hbudget : C ≤ ((r : ℝ) - 1) * c)
    (ξ : Fin n → Fin r → ℂ) (i : Fin n) (l : Fin r) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    copiedEnergy f r (copiedPattern i l z ξ) ≤ M ^ 2 * copiedEnergy f r ξ := by
  obtain ⟨h, hh, hzero, hone, hinter⟩ := hdef (copiedMean r ξ) i
  let w : Fin r → ℂ := elementaryPattern l z (fun _ => 1)
  have hw : ‖w l‖ ≤ 1 := by simpa [w, elementaryPattern] using hz
  have hwo : ∀ k, k ≠ l → w k = 0 ∨ w k = 1 := by
    intro k hkl
    by_cases hk : k < l
    · exact Or.inl (by simp [w, elementaryPattern, hk])
    · exact Or.inr (by simp [w, elementaryPattern, hk, hkl])
  have hmul (k : Fin r) : w k * ξ i k = elementaryPattern l z (ξ i) k := by
    simp only [w, elementaryPattern]
    split_ifs <;> simp
  have hlocal := coefficientDeficit_sum_nonneg l
    (replicationBase f (copiedMean r ξ) i) (replicationTail f (copiedMean r ξ) i)
    (f i) (ξ i) w hh hbudget hzero hone hinter hw hwo
  simp_rw [hmul] at hlocal
  have hvariance : (∑ j, if j = i then 0 else copiedVariance r (copiedPattern i l z ξ) j) ≤
      M ^ 2 * ∑ j, if j = i then 0 else copiedVariance r ξ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rcases lt_trichotomy j i with hji | hji | hij
    · simp only [if_neg hji.ne, copiedVariance_pattern_of_lt i l z ξ hji]
      exact mul_nonneg (sq_nonneg M) (copiedVariance_nonneg r ξ j)
    · subst j; simp
    · simp only [if_neg hij.ne', copiedVariance_pattern_of_gt i l z ξ hij]
      exact le_mul_of_one_le_left (copiedVariance_nonneg r ξ j) (by nlinarith)
  rw [copiedEnergy_group_decomposition f hr ξ i (hf i),
    copiedEnergy_group_decomposition f hr (copiedPattern i l z ξ) i (hf i)]
  change (∑ k, ‖replicationBase f (copiedMean r (copiedPattern i l z ξ)) i +
      copiedPattern i l z ξ i k • f i‖ ^ 2) + _ ≤ _
  rw [replicationBase_copiedPattern]
  simp only [copiedPattern_at]
  calc
    _ ≤ (M ^ 2 * ∑ k, ‖replicationBase f (copiedMean r ξ) i + ξ i k • f i‖ ^ 2) +
        (M ^ 2 * ∑ j, if j = i then 0 else copiedVariance r ξ j) :=
      add_le_add hlocal hvariance
    _ = _ := by rw [mul_add]; rfl

end ProofProject
