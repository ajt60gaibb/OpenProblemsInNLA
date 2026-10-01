import ProofProject.ReplicationEnergy

/-!
# Consecutive ordering of replicated coefficients

Copies are ordered first by their original coordinate and then by their copy
number. The numerical index is `i*r+l`; no arbitrary permutation is involved.
An elementary pattern therefore deletes whole earlier groups, applies one
elementary pattern inside its cut group, and retains whole later groups.
-/

noncomputable section

open scoped BigOperators

namespace ProofProject

variable {n r : ℕ}

/-- Flatten consecutive groups of copies in the source's order. -/
def copiedIndexEquiv : Fin n × Fin r ≃ Fin (n * r) := finProdFinEquiv

@[simp] lemma copiedIndexEquiv_val (i : Fin n) (l : Fin r) :
    (copiedIndexEquiv (i, l)).val = i.val * r + l.val := by
  simp only [copiedIndexEquiv, finProdFinEquiv_apply_val]
  ring

lemma copiedIndex_lt_of_group_lt {i j : Fin n} (hji : j < i) (k l : Fin r) :
    copiedIndexEquiv (j, k) < copiedIndexEquiv (i, l) := by
  change (copiedIndexEquiv (j, k)).val < (copiedIndexEquiv (i, l)).val
  rw [copiedIndexEquiv_val, copiedIndexEquiv_val]
  have hm := Nat.mul_le_mul_right r (show j.val + 1 ≤ i.val from hji)
  have hk := k.isLt
  nlinarith

lemma copiedIndex_lt_iff (j i : Fin n) (k l : Fin r) :
    copiedIndexEquiv (j, k) < copiedIndexEquiv (i, l) ↔
      j < i ∨ (j = i ∧ k < l) := by
  rcases lt_trichotomy j i with hji | hji | hij
  · simp [hji, copiedIndex_lt_of_group_lt hji]
  · subst j
    simp only [lt_self_iff_false, true_and, false_or]
    change (copiedIndexEquiv (i, k)).val < (copiedIndexEquiv (i, l)).val ↔ _
    rw [copiedIndexEquiv_val, copiedIndexEquiv_val]
    exact Nat.add_lt_add_iff_left
  · have hn := (copiedIndex_lt_of_group_lt hij l k).not_gt
    simp [hn, hij.not_gt, hij.ne']

@[simp] lemma copiedIndex_eq_iff (j i : Fin n) (k l : Fin r) :
    copiedIndexEquiv (j, k) = copiedIndexEquiv (i, l) ↔ j = i ∧ k = l := by
  rw [Equiv.apply_eq_iff_eq]
  simp only [Prod.mk.injEq]

/-- Reindexing between the two dimension expressions keeps every numerical
coordinate fixed, hence also keeps the entire order fixed. -/
def replicationDimensionEquiv (n r : ℕ) : Fin (n * r) ≃o Fin (r * n) :=
  Fin.castOrderIso (Nat.mul_comm n r)

@[simp] lemma replicationDimensionEquiv_val (k : Fin (n * r)) :
    (replicationDimensionEquiv n r k).val = k.val := rfl

/-- The copied coefficient array corresponding to the consecutive flattening. -/
def copiedCoefficients : (Fin (n * r) → ℂ) ≃ₗ[ℂ] (Fin n → Fin r → ℂ) where
  toFun c i l := c (copiedIndexEquiv (i, l))
  invFun ξ k := ξ (copiedIndexEquiv.symm k).1 (copiedIndexEquiv.symm k).2
  left_inv c := by
    funext k
    simp
  right_inv ξ := by
    funext i l
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma copiedCoefficients_apply (c : Fin (n * r) → ℂ) (i : Fin n) (l : Fin r) :
    copiedCoefficients c i l = c (copiedIndexEquiv (i, l)) := rfl

/-- The scalar multipliers inside the one partially retained group. -/
def copiedCutWeight (l : Fin r) (z : ℂ) (k : Fin r) : ℂ :=
  if k < l then 0 else if k = l then z else 1

@[simp] lemma copiedCutWeight_at (l : Fin r) (z : ℂ) : copiedCutWeight l z l = z := by
  simp [copiedCutWeight]

lemma copiedCutWeight_of_ne (l : Fin r) (z : ℂ) {k : Fin r} (hkl : k ≠ l) :
    copiedCutWeight l z k = 0 ∨ copiedCutWeight l z k = 1 := by
  unfold copiedCutWeight
  by_cases h : k < l <;> simp [h, hkl]

lemma norm_copiedCutWeight_le (l : Fin r) {z : ℂ} (hz : ‖z‖ ≤ 1) (k : Fin r) :
    ‖copiedCutWeight l z k‖ ≤ 1 := by
  by_cases hkl : k = l
  · subst k
    simpa using hz
  · rcases copiedCutWeight_of_ne l z hkl with h | h <;> simp [h]

lemma elementaryPattern_eq_copiedCutWeight_mul (l : Fin r) (z : ℂ)
    (c : Fin r → ℂ) (k : Fin r) :
    elementaryPattern l z c k = copiedCutWeight l z k * c k := by
  simp only [elementaryPattern, copiedCutWeight]
  split_ifs <;> simp

/-- The source elementary pattern at a group and a copy inside that group. -/
def copiedPattern (i : Fin n) (l : Fin r) (z : ℂ)
    (ξ : Fin n → Fin r → ℂ) (j : Fin n) (k : Fin r) : ℂ :=
  if j < i then 0 else if j = i then elementaryPattern l z (ξ j) k else ξ j k

lemma copiedPattern_of_lt (i : Fin n) (l : Fin r) (z : ℂ)
    (ξ : Fin n → Fin r → ℂ) {j : Fin n} (hji : j < i) :
    copiedPattern i l z ξ j = 0 := by
  funext k
  simp [copiedPattern, hji]

@[simp] lemma copiedPattern_at (i : Fin n) (l : Fin r) (z : ℂ)
    (ξ : Fin n → Fin r → ℂ) :
    copiedPattern i l z ξ i = elementaryPattern l z (ξ i) := by
  funext k
  simp [copiedPattern]

lemma copiedPattern_of_gt (i : Fin n) (l : Fin r) (z : ℂ)
    (ξ : Fin n → Fin r → ℂ) {j : Fin n} (hij : i < j) :
    copiedPattern i l z ξ j = ξ j := by
  funext k
  simp [copiedPattern, hij.not_gt, hij.ne']

/-- Flattened and grouped elementary patterns are exactly the same map. -/
theorem copiedCoefficients_elementaryPattern (i : Fin n) (l : Fin r) (z : ℂ)
    (c : Fin (n * r) → ℂ) :
    copiedCoefficients (elementaryPattern (copiedIndexEquiv (i, l)) z c) =
      copiedPattern i l z (copiedCoefficients c) := by
  funext j k
  simp only [copiedCoefficients_apply, elementaryPattern, copiedIndex_lt_iff,
    copiedIndex_eq_iff, copiedPattern]
  split_ifs <;> simp_all

/-- Earlier whole groups contribute zero mean. -/
lemma copiedMean_pattern_of_lt (i : Fin n) (l : Fin r) (z : ℂ)
    (ξ : Fin n → Fin r → ℂ) {j : Fin n} (hji : j < i) :
    copiedMean r (copiedPattern i l z ξ) j = 0 := by
  simp [copiedMean, copiedPattern_of_lt i l z ξ hji]

/-- Later whole groups keep their mean. -/
lemma copiedMean_pattern_of_gt (i : Fin n) (l : Fin r) (z : ℂ)
    (ξ : Fin n → Fin r → ℂ) {j : Fin n} (hij : i < j) :
    copiedMean r (copiedPattern i l z ξ) j = copiedMean r ξ j := by
  simp [copiedMean, copiedPattern_of_gt i l z ξ hij]

lemma copiedMean_pattern_at (i : Fin n) (l : Fin r) (z : ℂ)
    (ξ : Fin n → Fin r → ℂ) :
    copiedMean r (copiedPattern i l z ξ) i =
      (r : ℂ)⁻¹ * ∑ k, copiedCutWeight l z k * ξ i k := by
  simp [copiedMean, copiedPattern_at, elementaryPattern_eq_copiedCutWeight_mul]

/-- Earlier whole groups contribute zero variance. -/
lemma copiedVariance_pattern_of_lt (i : Fin n) (l : Fin r) (z : ℂ)
    (ξ : Fin n → Fin r → ℂ) {j : Fin n} (hji : j < i) :
    copiedVariance r (copiedPattern i l z ξ) j = 0 := by
  simp [copiedVariance, copiedMean_pattern_of_lt i l z ξ hji,
    copiedPattern_of_lt i l z ξ hji]

/-- Later whole groups keep their variance. -/
lemma copiedVariance_pattern_of_gt (i : Fin n) (l : Fin r) (z : ℂ)
    (ξ : Fin n → Fin r → ℂ) {j : Fin n} (hij : i < j) :
    copiedVariance r (copiedPattern i l z ξ) j = copiedVariance r ξ j := by
  simp [copiedVariance, copiedMean_pattern_of_gt i l z ξ hij,
    copiedPattern_of_gt i l z ξ hij]

/-- The dimension cast commutes with every elementary pattern, because it
changes neither coordinates nor their ordering. -/
theorem elementaryPattern_replicationDimension (i : Fin (n * r)) (z : ℂ)
    (c : Fin (r * n) → ℂ) :
    (fun j => elementaryPattern (replicationDimensionEquiv n r i) z c
      (replicationDimensionEquiv n r j)) =
        elementaryPattern i z (fun j => c (replicationDimensionEquiv n r j)) := by
  funext j
  simp only [elementaryPattern, OrderIso.lt_iff_lt, EmbeddingLike.apply_eq_iff_eq]

/-- Synthesis reindexing for the actual copied family. -/
theorem finiteSynthesis_copiedFamily {H : Type*} [AddCommMonoid H] [Module ℂ H]
    (f : Fin n × Fin r → H) (c : Fin (n * r) → ℂ) :
    (∑ k, c k • f (copiedIndexEquiv.symm k)) =
      ∑ i, ∑ l, copiedCoefficients c i l • f (i, l) := by
  calc
    _ = ∑ q : Fin n × Fin r, c (copiedIndexEquiv q) • f q := by
      simpa only [Equiv.symm_apply_apply] using
        (Equiv.sum_comp copiedIndexEquiv
          (fun k => c k • f (copiedIndexEquiv.symm k))).symm
    _ = _ := by rw [Fintype.sum_prod_type]; rfl

end ProofProject
