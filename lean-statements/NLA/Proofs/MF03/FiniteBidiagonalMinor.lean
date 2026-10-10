import NLA.Proofs.MF03.FiniteDeterminantLimit

/-!
The exact finite elementary Toeplitz matrices are minors of products of
upper-bidiagonal factor matrices. The determinant/tableau identity remains a
separate obligation.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

private noncomputable def finiteFactor (k : ℕ) : ℝ := cosineFactor (k + 1)

/-- One exact finite cosine factor as an upper-bidiagonal matrix. -/
noncomputable def finiteBidiagonal (m k : ℕ) :
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ :=
  fun i h => if h.val = i.val then 1 else
    if h.val = i.val + 1 then finiteFactor k else 0

/-- Factors are ordered `B_(N-1) ⋯ B_0`. -/
noncomputable def finiteBidiagonalProduct (m : ℕ) : ℕ →
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ
  | 0 => 1
  | N + 1 => finiteBidiagonal m N * finiteBidiagonalProduct m N

private theorem finiteElementary_zero (N : ℕ) :
    finiteCosineElementaryCoeff N 0 = 1 := by
  simp [finiteCosineElementaryCoeff]

private theorem finiteElementary_succ (N d : ℕ) :
    finiteCosineElementaryCoeff (N + 1) (d + 1) =
      finiteCosineElementaryCoeff N (d + 1) +
        finiteFactor N * finiteCosineElementaryCoeff N d := by
  let s : Finset ℕ := Finset.range N
  let w : Finset ℕ → ℝ := fun S => ∏ k ∈ S, finiteFactor k
  have hN : N ∉ s := by simp [s]
  have hdisj : Disjoint (s.powersetCard (d + 1))
      ((s.powersetCard d).image (insert N)) := by
    apply Finset.disjoint_left.mpr
    intro S hS hI
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hI
    have hsub := (Finset.mem_powersetCard.mp hS).1
    exact hN (hsub (Finset.mem_insert_self N T))
  have hinj : ∀ A ∈ s.powersetCard d, ∀ B ∈ s.powersetCard d,
      insert N A = insert N B → A = B := by
    intro A hA B hB hAB
    have ha : N ∉ A := fun h => hN ((Finset.mem_powersetCard.mp hA).1 h)
    have hb : N ∉ B := fun h => hN ((Finset.mem_powersetCard.mp hB).1 h)
    simpa [Finset.erase_insert ha, Finset.erase_insert hb] using
      congrArg (Finset.erase · N) hAB
  have hweight (S : Finset ℕ) (hS : S ∈ s.powersetCard d) :
      w (insert N S) = finiteFactor N * w S := by
    have hs : N ∉ S := fun h => hN ((Finset.mem_powersetCard.mp hS).1 h)
    simp [w, Finset.prod_insert hs]
  unfold finiteCosineElementaryCoeff
  change (∑ S ∈ (Finset.range (N + 1)).powersetCard (d + 1), w S) =
    (∑ S ∈ s.powersetCard (d + 1), w S) +
      finiteFactor N * ∑ S ∈ s.powersetCard d, w S
  rw [Finset.range_add_one, ← show Finset.range N = s from rfl,
    Finset.powersetCard_succ_insert hN d, Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image hinj]
  calc
    (∑ S ∈ s.powersetCard d, w (insert N S)) =
        ∑ S ∈ s.powersetCard d, finiteFactor N * w S := by
          apply Finset.sum_congr rfl
          intro S hS
          exact hweight S hS
    _ = finiteFactor N * ∑ S ∈ s.powersetCard d, w S := by
      rw [Finset.mul_sum]

private theorem finiteElementary_empty (d : ℕ) :
    finiteCosineElementaryCoeff 0 d = if d = 0 then 1 else 0 := by
  cases d with
  | zero => simp [finiteElementary_zero]
  | succ d =>
      unfold finiteCosineElementaryCoeff
      rw [Finset.range_zero]
      have h : (∅ : Finset ℕ).powersetCard (d + 1) = ∅ := by simp
      rw [h]
      simp

private theorem finiteBidiagonal_mul_apply_succ (m N : ℕ)
    (P : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ)
    (i h : Fin (2 * m + 1)) (hi : i.val + 1 < 2 * m + 1) :
    (finiteBidiagonal m N * P) i h =
      P i h + finiteFactor N * P ⟨i.val + 1, hi⟩ h := by
  let i' : Fin (2 * m + 1) := ⟨i.val + 1, hi⟩
  have hb (x : Fin (2 * m + 1)) :
      finiteBidiagonal m N i x =
        (if x = i then 1 else 0) +
          (if x = i' then finiteFactor N else 0) := by
    by_cases hxi : x = i
    · subst x
      have hne : i ≠ i' := by
        intro heq
        have hv := congrArg Fin.val heq
        dsimp [i'] at hv
        omega
      simp [finiteBidiagonal, i', hne]
    · by_cases hxs : x = i'
      · subst x
        simp [finiteBidiagonal, i', hxi]
      · have hval₁ : x.val ≠ i.val := fun heq => hxi (Fin.ext heq)
        have hval₂ : x.val ≠ i.val + 1 := by
          intro heq
          exact hxs (Fin.ext (by simpa [i'] using heq))
        simp [finiteBidiagonal, hxi, hxs, hval₁, hval₂]
  simp [Matrix.mul_apply, hb, add_mul, Finset.sum_add_distrib, i']

private theorem finiteBidiagonal_mul_apply_last (m N : ℕ)
    (P : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ)
    (i h : Fin (2 * m + 1)) (hi : ¬ i.val + 1 < 2 * m + 1) :
    (finiteBidiagonal m N * P) i h = P i h := by
  have hb (x : Fin (2 * m + 1)) :
      finiteBidiagonal m N i x = if x = i then 1 else 0 := by
    by_cases hxi : x = i
    · subst x
      simp [finiteBidiagonal]
    · have hval₁ : x.val ≠ i.val := fun heq => hxi (Fin.ext heq)
      have hval₂ : x.val ≠ i.val + 1 := by
        have hx := x.isLt
        omega
      simp [finiteBidiagonal, hxi, hval₁, hval₂]
  simp [Matrix.mul_apply, hb]

/-- Every entry is the exact finite elementary coefficient above the diagonal. -/
theorem finiteBidiagonalProduct_entry (m N : ℕ)
    (i h : Fin (2 * m + 1)) :
    finiteBidiagonalProduct m N i h =
      if i.val ≤ h.val then
        finiteCosineElementaryCoeff N (h.val - i.val) else 0 := by
  induction N generalizing i h with
  | zero =>
      simp only [finiteBidiagonalProduct, finiteElementary_empty]
      by_cases heq : i = h
      · subst h
        simp
      · have hval : i.val ≠ h.val := fun hval => heq (Fin.ext hval)
        by_cases hlt : i.val < h.val
        · have hne : h.val - i.val ≠ 0 := by omega
          simp [heq, Nat.le_of_lt hlt, hne]
        · have hnle : ¬ i.val ≤ h.val := by omega
          simp [heq, hnle]
  | succ N ih =>
      simp only [finiteBidiagonalProduct]
      by_cases hi : i.val + 1 < 2 * m + 1
      · rw [finiteBidiagonal_mul_apply_succ m N
          (finiteBidiagonalProduct m N) i h hi,
          ih i h, ih (⟨i.val + 1, hi⟩ : Fin (2 * m + 1)) h]
        by_cases hlt : i.val < h.val
        · have hle : i.val ≤ h.val := Nat.le_of_lt hlt
          have hle' : i.val + 1 ≤ h.val := by omega
          simp only [if_pos hle, if_pos hle']
          have hd : h.val - i.val = (h.val - (i.val + 1)) + 1 := by omega
          rw [hd, finiteElementary_succ]
        · by_cases heq : i.val = h.val
          · simp [heq, finiteElementary_zero]
          · have hnot : ¬ i.val ≤ h.val := by omega
            have hnot' : ¬ i.val + 1 ≤ h.val := by omega
            simp [hnot, hnot']
      · rw [finiteBidiagonal_mul_apply_last m N
          (finiteBidiagonalProduct m N) i h hi, ih i h]
        have hnot : ¬ i.val < h.val := by
          have hh := h.isLt
          omega
        by_cases heq : i.val = h.val
        · simp [heq, finiteElementary_zero]
        · have hnle : ¬ i.val ≤ h.val := by omega
          simp [hnle]

/-- Rows of the augmented minor omit exactly index `j`. -/
def finiteMinorRow (m j : ℕ) (r : Fin m) : Fin (2 * m + 1) :=
  ⟨if r.val < j then r.val else r.val + 1, by
    have hr := r.isLt
    split_ifs <;> omega⟩

/-- The columns of both minors occupy positions `m+1,…,2m`. -/
def finiteMinorCol (m : ℕ) (c : Fin m) : Fin (2 * m + 1) :=
  ⟨m + 1 + c.val, by omega⟩

/-- The finite augmented determinant is exactly the indicated product minor. -/
theorem finiteCosineAugDet_eq_bidiagonal_minor (N m j : ℕ) (_hj : j ≤ m) :
    finiteCosineAugDet N m j =
      Matrix.det (fun r c : Fin m =>
        finiteBidiagonalProduct m N (finiteMinorRow m j r) (finiteMinorCol m c)) := by
  unfold finiteCosineAugDet
  congr 1
  funext r c
  rw [finiteBidiagonalProduct_entry]
  have hle : (finiteMinorRow m j r).val ≤ (finiteMinorCol m c).val := by
    simp only [finiteMinorRow, finiteMinorCol]
    have hr := r.isLt
    split_ifs <;> omega
  rw [if_pos hle]
  change finiteCosineElementaryCoeff N
      (m + (if r.val < j then 1 else 0) + c.val - r.val) =
    finiteCosineElementaryCoeff N
      (m + 1 + c.val - (if r.val < j then r.val else r.val + 1))
  congr 1
  split_ifs <;> omega

/-- At `j=0` this is the rectangular determinant minor. -/
theorem finiteCosineRectDet_eq_bidiagonal_minor (N m : ℕ) :
    finiteCosineRectDet N m =
      Matrix.det (fun r c : Fin m =>
        finiteBidiagonalProduct m N (finiteMinorRow m 0 r) (finiteMinorCol m c)) := by
  rw [← finiteCosineAugDet_zero]
  exact finiteCosineAugDet_eq_bidiagonal_minor N m 0 (Nat.zero_le m)

#assert_trust kernel finiteBidiagonalProduct_entry
#assert_trust kernel finiteCosineAugDet_eq_bidiagonal_minor
#assert_trust kernel finiteCosineRectDet_eq_bidiagonal_minor
#print axioms finiteCosineAugDet_eq_bidiagonal_minor

end NLA.Proofs.MF03
