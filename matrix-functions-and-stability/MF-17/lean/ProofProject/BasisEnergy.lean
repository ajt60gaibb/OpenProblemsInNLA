import ProofProject.Definitions

/-!
# Finite synthesis and coefficient-energy comparisons

These estimates use only a finite family of unit vectors. In particular, the
coordinate estimate required for the metric perturbation follows directly from
bounds on adjacent tails, without a Gram-matrix inverse.
-/

noncomputable section

open scoped BigOperators

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H] {N : ℕ}

/-- Synthesis of a finite complex coefficient vector. -/
def finiteSynthesis (f : Fin N → H) (c : Fin N → ℂ) : H :=
  ∑ j, c j • f j

/-- Euclidean squared norm of the coefficient vector. -/
def coefficientEnergy (c : Fin N → ℂ) : ℝ := ∑ j, ‖c j‖ ^ 2

/-- A tail starts at coordinate `k`; the tail at `N` is zero. -/
def synthesisTail (f : Fin N → H) (c : Fin N → ℂ) (k : ℕ) : H :=
  ∑ j, if k ≤ j.val then c j • f j else 0

/-- The source elementary pattern deletes coordinates before `i`, multiplies
coordinate `i` by `z`, and leaves all later coordinates unchanged. -/
def elementaryPattern (i : Fin N) (z : ℂ) (c : Fin N → ℂ) (j : Fin N) : ℂ :=
  if j < i then 0 else if j = i then z * c j else c j

theorem coefficientEnergy_nonneg (c : Fin N → ℂ) : 0 ≤ coefficientEnergy c :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- A nonzero coefficient vector has strictly positive Euclidean energy. -/
theorem coefficientEnergy_pos {c : Fin N → ℂ} (hc : c ≠ 0) :
    0 < coefficientEnergy c := by
  have hne : ∃ j, c j ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  obtain ⟨j, hj⟩ := hne
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
    ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hj)⟩

theorem coefficientEnergy_eq_zero_iff {c : Fin N → ℂ} :
    coefficientEnergy c = 0 ↔ c = 0 := by
  constructor
  · intro h
    by_contra hc
    exact (ne_of_gt (coefficientEnergy_pos hc)) h
  · rintro rfl
    simp [coefficientEnergy]

/-- Every elementary pattern is a contraction for Euclidean coefficient
energy, independently of the Hilbert metric placed on synthesized vectors. -/
theorem coefficientEnergy_elementaryPattern_le (i : Fin N) (z : ℂ)
    (c : Fin N → ℂ) (hz : ‖z‖ ≤ 1) :
    coefficientEnergy (elementaryPattern i z c) ≤ coefficientEnergy c := by
  apply Finset.sum_le_sum
  intro j _
  by_cases hlt : j < i
  · simp only [elementaryPattern, hlt, ite_true, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _
  · by_cases heq : j = i
    · subst j
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa [elementaryPattern, norm_mul] using
        mul_le_mul_of_nonneg_right hz (norm_nonneg (c i))
    · simp only [elementaryPattern, hlt, heq, ite_false, le_refl]

/-- The triangle inequality followed by finite Cauchy--Schwarz. -/
theorem finiteSynthesis_norm_sq_le (f : Fin N → H) (c : Fin N → ℂ)
    (hf : ∀ j, ‖f j‖ = 1) :
    ‖finiteSynthesis f c‖ ^ 2 ≤ (N : ℝ) * coefficientEnergy c := by
  have htriangle : ‖finiteSynthesis f c‖ ≤ ∑ j, ‖c j‖ := by
    simpa only [finiteSynthesis, norm_smul, hf, mul_one] using
      norm_sum_le (s := Finset.univ) (f := fun j => c j • f j)
  calc
    ‖finiteSynthesis f c‖ ^ 2 ≤ (∑ j, ‖c j‖) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    _ ≤ (N : ℝ) * coefficientEnergy c := by
      simpa only [Finset.card_univ, Fintype.card_fin, coefficientEnergy] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖c j‖))

/-- Coordinate bounds control coefficient energy with the explicit factor
needed by the exact-`M` metric perturbation. -/
theorem coefficientEnergy_le_of_coordinate_bound
    (f : Fin N → H) (c : Fin N → ℂ) (M : ℝ)
    (hf : ∀ j, ‖f j‖ = 1)
    (hcoord : ∀ j, ‖c j • f j‖ ≤ 2 * M * ‖finiteSynthesis f c‖) :
    coefficientEnergy c ≤ 4 * M ^ 2 * (N : ℝ) * ‖finiteSynthesis f c‖ ^ 2 := by
  have hterm (j : Fin N) :
      ‖c j‖ ^ 2 ≤ 4 * M ^ 2 * ‖finiteSynthesis f c‖ ^ 2 := by
    have hj : ‖c j‖ ≤ 2 * M * ‖finiteSynthesis f c‖ := by
      simpa only [norm_smul, hf, mul_one] using hcoord j
    calc
      ‖c j‖ ^ 2 ≤ (2 * M * ‖finiteSynthesis f c‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hj 2
      _ = 4 * M ^ 2 * ‖finiteSynthesis f c‖ ^ 2 := by ring
  calc
    coefficientEnergy c ≤ ∑ _j : Fin N, 4 * M ^ 2 * ‖finiteSynthesis f c‖ ^ 2 :=
      Finset.sum_le_sum fun j _ => hterm j
    _ = 4 * M ^ 2 * (N : ℝ) * ‖finiteSynthesis f c‖ ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem synthesisTail_zero (f : Fin N → H) (c : Fin N → ℂ) :
    synthesisTail f c 0 = finiteSynthesis f c := by
  simp [synthesisTail, finiteSynthesis]

theorem synthesisTail_length (f : Fin N → H) (c : Fin N → ℂ) :
    synthesisTail f c N = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact if_neg (Nat.not_le_of_gt j.isLt)

theorem synthesisTail_eq_zero_of_length_le (f : Fin N → H)
    (c : Fin N → ℂ) {k : ℕ} (hk : N ≤ k) : synthesisTail f c k = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact if_neg (by omega)

/-- A tail starting inside the index set is the elementary pattern with
multiplier one. -/
theorem finiteSynthesis_elementaryPattern_one
    (f : Fin N → H) (c : Fin N → ℂ) (i : Fin N) :
    finiteSynthesis f (elementaryPattern i 1 c) = synthesisTail f c i.val := by
  unfold finiteSynthesis synthesisTail
  apply Finset.sum_congr rfl
  intro j _
  by_cases hlt : j < i
  · have hnot : ¬i.val ≤ j.val := by omega
    simp [elementaryPattern, hlt, hnot]
  · have hle : i.val ≤ j.val := by omega
    simp [elementaryPattern, hlt, hle]

/-- A common bound for all elementary patterns bounds every tail, including
the empty tails at and beyond `N`. The assumption concerns this coefficient
vector only, so it also follows from an operator-norm bound on each pattern. -/
theorem tail_bound_of_elementaryPattern_bound
    (f : Fin N → H) (c : Fin N → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hpattern : ∀ (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 →
      ‖finiteSynthesis f (elementaryPattern i z c)‖ ≤ M * ‖finiteSynthesis f c‖)
    (k : ℕ) : ‖synthesisTail f c k‖ ≤ M * ‖finiteSynthesis f c‖ := by
  by_cases hk : k < N
  · rw [← finiteSynthesis_elementaryPattern_one f c ⟨k, hk⟩]
    exact hpattern _ 1 (by simp)
  · rw [synthesisTail_eq_zero_of_length_le f c (Nat.le_of_not_gt hk), norm_zero]
    exact mul_nonneg hM (norm_nonneg _)

/-- Adjacent tails isolate the contribution of one coordinate. -/
theorem synthesisTail_sub_succ (f : Fin N → H) (c : Fin N → ℂ) (j : Fin N) :
    synthesisTail f c j.val - synthesisTail f c (j.val + 1) = c j • f j := by
  simp only [synthesisTail, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    by_cases hle : j.val ≤ i.val
    · have hlt : j.val + 1 ≤ i.val := by omega
      simp [hle, hlt]
    · have hlt : ¬ j.val + 1 ≤ i.val := by omega
      simp [hle, hlt]
  · simp

/-- Tail bounds imply the coordinate bound in the same ambient norm. This
lemma may therefore be applied again after changing the Hilbert metric. -/
theorem coordinate_bound_of_tail_bound
    (f : Fin N → H) (c : Fin N → ℂ) (M : ℝ)
    (htail : ∀ k : ℕ, ‖synthesisTail f c k‖ ≤ M * ‖finiteSynthesis f c‖)
    (j : Fin N) : ‖c j • f j‖ ≤ 2 * M * ‖finiteSynthesis f c‖ := by
  rw [← synthesisTail_sub_succ f c j]
  calc
    ‖synthesisTail f c j.val - synthesisTail f c (j.val + 1)‖ ≤
        ‖synthesisTail f c j.val‖ + ‖synthesisTail f c (j.val + 1)‖ := norm_sub_le _ _
    _ ≤ M * ‖finiteSynthesis f c‖ + M * ‖finiteSynthesis f c‖ :=
      add_le_add (htail _) (htail _)
    _ = 2 * M * ‖finiteSynthesis f c‖ := by ring

theorem coefficientEnergy_le_of_tail_bound
    (f : Fin N → H) (c : Fin N → ℂ) (M : ℝ)
    (hf : ∀ j, ‖f j‖ = 1)
    (htail : ∀ k : ℕ, ‖synthesisTail f c k‖ ≤ M * ‖finiteSynthesis f c‖) :
    coefficientEnergy c ≤ 4 * M ^ 2 * (N : ℝ) * ‖finiteSynthesis f c‖ ^ 2 :=
  coefficientEnergy_le_of_coordinate_bound f c M hf
    (coordinate_bound_of_tail_bound f c M htail)

/-- The source's elementary-pattern hypothesis supplies the coefficient
energy bound required by the metric-margin construction. -/
theorem coefficientEnergy_le_of_elementaryPattern_bound
    (f : Fin N → H) (c : Fin N → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ j, ‖f j‖ = 1)
    (hpattern : ∀ (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 →
      ‖finiteSynthesis f (elementaryPattern i z c)‖ ≤ M * ‖finiteSynthesis f c‖) :
    coefficientEnergy c ≤ 4 * M ^ 2 * (N : ℝ) * ‖finiteSynthesis f c‖ ^ 2 :=
  coefficientEnergy_le_of_tail_bound f c M hf
    (tail_bound_of_elementaryPattern_bound f c M hM hpattern)

end ProofProject
