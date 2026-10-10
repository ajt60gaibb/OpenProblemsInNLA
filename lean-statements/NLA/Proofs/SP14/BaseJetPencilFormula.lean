import NLA.Proofs.SP14.BaseJetFourierMatrix

/-!
The finite base-pencil calculation for the actual exterior symbol with
one current restored negative packet. This is the source's exact model
jet formula, not a perturbed-background stage theorem.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped Polynomial

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

noncomputable def baseJetE (m q : ℕ) (v : Fin q → ℂ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  fun i j => ∑ d : Fin q,
    if j.val = i.val + (m - d.val) then v d else 0

private theorem baseJetG_eq (m q : ℕ) (v : Fin q → ℂ) :
    baseJetG m q v = baseG m + baseJetE m q v := by
  ext i j
  rfl

private theorem baseUpperShift_pow_apply (m r : ℕ)
    (i j : Fin (m + 1)) :
    (baseUpperShift m ^ r) i j =
      if j.val = i.val + r then 1 else 0 := by
  induction r generalizing j with
  | zero =>
      simp [Matrix.one_apply, Fin.ext_iff, eq_comm]
  | succ r ih =>
      rw [pow_succ, Matrix.mul_apply]
      simp_rw [ih]
      by_cases hindex : i.val + r < m + 1
      · let k : Fin (m + 1) := ⟨i.val + r, hindex⟩
        rw [Finset.sum_eq_single k]
        · simp [k, baseUpperShift, Nat.add_assoc]
        · intro b hb hbk
          have hneq : b.val ≠ i.val + r := by
            intro heq
            exact hbk (Fin.ext heq)
          simp [hneq]
        · intro hk
          exact (hk (Finset.mem_univ k)).elim
      · have hnone : ∀ k : Fin (m + 1), k.val ≠ i.val + r := by
          intro k
          have hk := k.isLt
          omega
        have hnone2 : j.val ≠ i.val + (r + 1) := by
          have hj := j.isLt
          omega
        simp [hnone, hnone2]

private theorem baseUpperShift_pow_zero (m r : ℕ) (hr : m + 1 ≤ r) :
    baseUpperShift m ^ r = 0 := by
  ext i j
  rw [baseUpperShift_pow_apply]
  have hne : j.val ≠ i.val + r := by
    have hj := j.isLt
    omega
  simp [hne]

private theorem baseJetE_eq_shift_sum (m q : ℕ) (v : Fin q → ℂ) :
    baseJetE m q v =
      ∑ d : Fin q, v d • baseUpperShift m ^ (m - d.val) := by
  ext i j
  simp [baseJetE, baseUpperShift_pow_apply, Matrix.sum_apply, Matrix.smul_apply]

private theorem baseG_commute_shift (m : ℕ) :
    baseG m * baseUpperShift m = baseUpperShift m * baseG m := by
  have hU : baseUpperShift m = baseG m * baseG m - 1 := by
    calc
      baseUpperShift m = (1 + baseUpperShift m) - 1 := by abel
      _ = baseG m * baseG m - 1 := by rw [baseG_square]
  rw [hU]
  noncomm_ring

private theorem baseG_commute_E (m q : ℕ) (v : Fin q → ℂ) :
    baseG m * baseJetE m q v = baseJetE m q v * baseG m := by
  rw [baseJetE_eq_shift_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have hc : Commute (baseG m) (baseUpperShift m) :=
    baseG_commute_shift m
  rw [Matrix.mul_smul, Matrix.smul_mul, hc.pow_right (m - d.val)]

private theorem baseJetE_zero_below (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) (i j : Fin (m + 1))
    (hij : j.val < i.val + (m - q + 1)) :
    baseJetE m q v i j = 0 := by
  unfold baseJetE
  apply Finset.sum_eq_zero
  intro d hd
  have hdlt := d.isLt
  have hne : j.val ≠ i.val + (m - d.val) := by omega
  simp [hne]

private theorem baseJetE_square_zero (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) :
    baseJetE m q v * baseJetE m q v = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hik : k.val < i.val + (m - q + 1)
  · rw [baseJetE_zero_below m q hq v i k hik]
    simp
  · have hkj : j.val < k.val + (m - q + 1) := by
      have hj := j.isLt
      omega
    rw [baseJetE_zero_below m q hq v k j hkj]
    simp

private theorem baseJetG_square (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) :
    baseJetG m q v * baseJetG m q v =
      1 + baseUpperShift m + (2 : ℂ) • (baseG m * baseJetE m q v) := by
  rw [baseJetG_eq]
  calc
    (baseG m + baseJetE m q v) * (baseG m + baseJetE m q v) =
        baseG m * baseG m + baseG m * baseJetE m q v +
          baseJetE m q v * baseG m + baseJetE m q v * baseJetE m q v := by
      noncomm_ring
    _ = 1 + baseUpperShift m +
          baseG m * baseJetE m q v + baseG m * baseJetE m q v := by
      rw [baseG_square, baseG_commute_E m q v, baseJetE_square_zero m q hq v]
      abel
    _ = 1 + baseUpperShift m + (2 : ℂ) • (baseG m * baseJetE m q v) := by
      rw [two_smul]
      abel

private theorem baseJet_pencil_eq (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) (t : ℂ) :
    baseJetG m q v * baseJetG m q v -
        (t + 1) • baseUpperShift m =
      1 - t • baseUpperShift m +
        (2 : ℂ) • (baseG m * baseJetE m q v) := by
  rw [baseJetG_square m q hq v, add_smul, one_smul]
  abel

private noncomputable def baseJetW (m : ℕ) (t : ℂ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  ∑ k ∈ Finset.range (m + 1), (t • baseUpperShift m) ^ k

private theorem baseJetN_pow_zero (m : ℕ) (t : ℂ) :
    (t • baseUpperShift m) ^ (m + 1) = 0 := by
  rw [smul_pow, baseUpperShift_pow_zero m (m + 1) (by omega), smul_zero]

private theorem baseJetW_mul (m : ℕ) (t : ℂ) :
    baseJetW m t * (1 - t • baseUpperShift m) = 1 := by
  unfold baseJetW
  rw [geom_sum_mul_neg, baseJetN_pow_zero, sub_zero]

private theorem baseJet_mul_W (m : ℕ) (t : ℂ) :
    (1 - t • baseUpperShift m) * baseJetW m t = 1 := by
  unfold baseJetW
  rw [mul_neg_geom_sum, baseJetN_pow_zero, sub_zero]

private theorem baseJetE_commute_shift (m q : ℕ) (v : Fin q → ℂ) :
    baseJetE m q v * baseUpperShift m =
      baseUpperShift m * baseJetE m q v := by
  rw [baseJetE_eq_shift_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Matrix.smul_mul, Matrix.mul_smul]
  exact congrArg (v d • ·) (Commute.pow_left (Commute.refl (baseUpperShift m)) _).eq

private theorem baseJetA_commute_shift (m q : ℕ) (v : Fin q → ℂ) :
    (baseG m * baseJetE m q v) * baseUpperShift m =
      baseUpperShift m * (baseG m * baseJetE m q v) := by
  calc
    (baseG m * baseJetE m q v) * baseUpperShift m =
        baseG m * (baseUpperShift m * baseJetE m q v) := by
          rw [← baseJetE_commute_shift]; simp only [mul_assoc]
    _ = baseUpperShift m * (baseG m * baseJetE m q v) := by
      rw [← mul_assoc, baseG_commute_shift, mul_assoc]

private theorem baseJetA_square_zero (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) :
    (baseG m * baseJetE m q v) * (baseG m * baseJetE m q v) = 0 := by
  calc
    (baseG m * baseJetE m q v) * (baseG m * baseJetE m q v) =
        baseG m * ((baseJetE m q v * baseG m) * baseJetE m q v) := by
          simp only [mul_assoc]
    _ = (baseG m * baseG m) * (baseJetE m q v * baseJetE m q v) := by
      rw [← baseG_commute_E m q v]
      simp only [mul_assoc]
    _ = 0 := by rw [baseJetE_square_zero m q hq v, mul_zero]

private theorem baseJetA_commute_N (m q : ℕ) (v : Fin q → ℂ) (t : ℂ) :
    (baseG m * baseJetE m q v) * (t • baseUpperShift m) =
      (t • baseUpperShift m) * (baseG m * baseJetE m q v) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, baseJetA_commute_shift]

private theorem baseJetA_commute_W (m q : ℕ) (v : Fin q → ℂ) (t : ℂ) :
    (baseG m * baseJetE m q v) * baseJetW m t =
      baseJetW m t * (baseG m * baseJetE m q v) := by
  unfold baseJetW
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  exact (Commute.pow_right (baseJetA_commute_N m q v t) k).eq

private theorem baseJetAW_square_zero (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) (t : ℂ) :
    ((baseG m * baseJetE m q v) * baseJetW m t) *
        ((baseG m * baseJetE m q v) * baseJetW m t) = 0 := by
  let A := baseG m * baseJetE m q v
  let W := baseJetW m t
  have hcomm : A * W = W * A := baseJetA_commute_W m q v t
  have hnil : A * A = 0 := baseJetA_square_zero m q hq v
  calc
    (A * W) * (A * W) = (A * A) * (W * W) := by
      calc
        (A * W) * (A * W) = A * (W * A) * W := by simp only [mul_assoc]
        _ = (A * A) * (W * W) := by rw [← hcomm]; simp only [mul_assoc]
    _ = 0 := by rw [hnil, zero_mul]

private theorem baseJet_pencil_mul_candidate (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) (t : ℂ) :
    (baseJetG m q v * baseJetG m q v - (t + 1) • baseUpperShift m) *
        (baseJetW m t - (2 : ℂ) •
          (baseJetW m t * (baseG m * baseJetE m q v) * baseJetW m t)) = 1 := by
  let F := 1 - t • baseUpperShift m
  let W := baseJetW m t
  let A := baseG m * baseJetE m q v
  have hFW : F * W = 1 := baseJet_mul_W m t
  have hnil : (A * W) * (A * W) = 0 := baseJetAW_square_zero m q hq v t
  rw [baseJet_pencil_eq m q hq v t]
  change (F + (2 : ℂ) • A) * (W - (2 : ℂ) • (W * A * W)) = 1
  rw [two_smul, two_smul]
  calc
    (F + (A + A)) * (W - (W * A * W + W * A * W)) =
        F * W - (F * W) * A * W - (F * W) * A * W +
          A * W + A * W -
          (A * W) * (A * W) - (A * W) * (A * W) -
          (A * W) * (A * W) - (A * W) * (A * W) := by noncomm_ring
    _ = 1 := by rw [hFW, hnil]; noncomm_ring

private theorem baseJetA_zero_below (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) (i j : Fin (m + 1)) (hji : j.val ≤ i.val) :
    (baseG m * baseJetE m q v) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hik : i.val ≤ k.val
  · have hjk : j.val < k.val + (m - q + 1) := by omega
    rw [baseJetE_zero_below m q hq v k j hjk]
    simp
  · have hki : ¬ i.val ≤ k.val := hik
    simp [baseG, hki]

private theorem baseJet_pencil_upper (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) (t : ℂ) :
    (baseJetG m q v * baseJetG m q v -
      (t + 1) • baseUpperShift m).IsUpperTriangular := by
  intro i j hji
  have hle : j.val ≤ i.val := by exact le_of_lt hji
  have hne : i ≠ j := by intro h; subst j; exact (lt_irrefl i) hji
  have hshift : j.val ≠ i.val + 1 := by omega
  rw [baseJet_pencil_eq m q hq v t]
  simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    baseUpperShift, baseJetA_zero_below m q hq v i j hle,
    hne, hshift]

private theorem baseJet_pencil_diag (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) (t : ℂ) (i : Fin (m + 1)) :
    (baseJetG m q v * baseJetG m q v -
      (t + 1) • baseUpperShift m) i i = 1 := by
  rw [baseJet_pencil_eq m q hq v t]
  simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    baseUpperShift, baseJetA_zero_below m q hq v i i (le_refl _)]

private theorem baseJet_pencil_det (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) (t : ℂ) :
    (baseJetG m q v * baseJetG m q v -
      (t + 1) • baseUpperShift m).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (baseJet_pencil_upper m q hq v t)]
  simp_rw [baseJet_pencil_diag m q hq v t]
  simp

private theorem baseJet_pencil_adjugate (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) (t : ℂ) :
    (baseJetG m q v * baseJetG m q v -
      (t + 1) • baseUpperShift m).adjugate =
        baseJetW m t - (2 : ℂ) •
          (baseJetW m t * (baseG m * baseJetE m q v) * baseJetW m t) := by
  let H := baseJetG m q v * baseJetG m q v -
    (t + 1) • baseUpperShift m
  let N := baseJetW m t - (2 : ℂ) •
    (baseJetW m t * (baseG m * baseJetE m q v) * baseJetW m t)
  have hHN : H * N = 1 := baseJet_pencil_mul_candidate m q hq v t
  have hdet : H.det = 1 := baseJet_pencil_det m q hq v t
  change H.adjugate = N
  calc
    H.adjugate = (H.adjugate * H) * N := by rw [mul_assoc, hHN, mul_one]
    _ = N := by rw [Matrix.adjugate_mul, hdet]; simp

private theorem baseJetW_apply (m : ℕ) (t : ℂ) (i j : Fin (m + 1)) :
    baseJetW m t i j =
      if i.val ≤ j.val then t ^ (j.val - i.val) else 0 := by
  unfold baseJetW
  rw [Matrix.sum_apply]
  by_cases hij : i.val ≤ j.val
  · rw [Finset.sum_eq_single (j.val - i.val)]
    · rw [smul_pow, Matrix.smul_apply, baseUpperShift_pow_apply]
      have heq : j.val = i.val + (j.val - i.val) := by omega
      rw [if_pos heq]
      simp only [smul_eq_mul, mul_one, if_pos hij]
    · intro k hk hneq
      rw [smul_pow, Matrix.smul_apply, baseUpperShift_pow_apply]
      have hno : j.val ≠ i.val + k := by omega
      simp [hno]
    · intro hnot
      have hmem : j.val - i.val ∈ Finset.range (m + 1) := by
        have hj := j.isLt
        simp only [Finset.mem_range]
        omega
      exact (hnot hmem).elim
  · rw [Finset.sum_eq_zero]
    · simp [hij]
    · intro k hk
      rw [smul_pow, Matrix.smul_apply, baseUpperShift_pow_apply]
      have hno : j.val ≠ i.val + k := by omega
      simp [hno]

private theorem baseJetW_corner (m : ℕ) (t : ℂ) :
    baseJetW m t 0 (Fin.last m) = t ^ m := by
  rw [baseJetW_apply]
  simp

private theorem baseJetW_square_top (m : ℕ) (t : ℂ)
    (j : Fin (m + 1)) :
    (baseJetW m t * baseJetW m t) 0 j =
      ((j.val + 1 : ℕ) : ℂ) * t ^ j.val := by
  rw [Matrix.mul_apply]
  have hterm (k : Fin (m + 1)) :
      baseJetW m t 0 k * baseJetW m t k j =
        if k ≤ j then t ^ j.val else 0 := by
    rw [baseJetW_apply, baseJetW_apply]
    by_cases hkj : k ≤ j
    · have hsum : k.val + (j.val - k.val) = j.val := by omega
      simp [hkj, ← pow_add, hsum]
    · simp [hkj]
  simp_rw [hterm]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  have hfilter : (Finset.univ.filter fun k : Fin (m + 1) => k ≤ j) =
      Finset.Iic j := by ext k; simp
  rw [hfilter, Finset.sum_const, Fin.card_Iic]
  simp [nsmul_eq_mul]

private theorem baseJetW_square_G_top (m : ℕ) (t : ℂ)
    (j : Fin (m + 1)) :
    ((baseJetW m t * baseJetW m t) * baseG m) 0 j =
      ∑ k ∈ Finset.range (j.val + 1),
        (((k + 1 : ℕ) : ℂ) * baseCoeff (j.val - k)) * t ^ k := by
  let f : ℕ → ℂ := fun k =>
    (((k + 1 : ℕ) : ℂ) * baseCoeff (j.val - k)) * t ^ k
  have hsum :
      ((baseJetW m t * baseJetW m t) * baseG m) 0 j =
        ∑ k ∈ Finset.range (m + 1), if k ≤ j.val then f k else 0 := by
    rw [Matrix.mul_apply, Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k < m + 1 := Finset.mem_range.mp hk
    by_cases hkj : k ≤ j.val
    · simp [f, hkm, hkj, baseG, baseJetW_square_top]
      ring
    · simp [f, hkm, hkj, baseG]
  rw [hsum]
  have hsubset : Finset.range (j.val + 1) ⊆ Finset.range (m + 1) := by
    intro k hk
    have hj := j.isLt
    simp only [Finset.mem_range] at hk ⊢
    omega
  calc
    (∑ k ∈ Finset.range (m + 1), if k ≤ j.val then f k else 0) =
        ∑ k ∈ Finset.range (j.val + 1), if k ≤ j.val then f k else 0 := by
      symm
      apply Finset.sum_subset hsubset
      intro k hk hnot
      have hkgt : j.val < k := by
        simp only [Finset.mem_range] at hnot
        omega
      simp [not_le.mpr hkgt]
    _ = ∑ k ∈ Finset.range (j.val + 1), f k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkj : k ≤ j.val := by
        simp only [Finset.mem_range] at hk
        omega
      simp [hkj]

private theorem baseJet_mul_shift_corner (m : ℕ)
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (d : Fin (m + 1)) :
    (M * baseUpperShift m ^ (m - d.val)) 0 (Fin.last m) = M 0 d := by
  rw [Matrix.mul_apply, Finset.sum_eq_single d]
  · rw [baseUpperShift_pow_apply]
    have heq : (Fin.last m).val = d.val + (m - d.val) := by
      simp only [Fin.val_last]
      omega
    rw [if_pos heq]
    simp
  · intro k hk hkd
    rw [baseUpperShift_pow_apply]
    have hne : (Fin.last m).val ≠ k.val + (m - d.val) := by
      simp only [Fin.val_last]
      intro heq
      apply hkd
      apply Fin.ext
      omega
    rw [if_neg hne]
    simp
  · intro hnot
    exact (hnot (Finset.mem_univ d)).elim

private theorem baseJetW_A_W_corner (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) (t : ℂ) :
    (baseJetW m t * (baseG m * baseJetE m q v) * baseJetW m t)
        0 (Fin.last m) =
      ∑ d : Fin q, v d *
        (∑ k ∈ Finset.range (d.val + 1),
          (((k + 1 : ℕ) : ℂ) * baseCoeff (d.val - k)) * t ^ k) := by
  let W := baseJetW m t
  let G := baseG m
  let E := baseJetE m q v
  have hcomm : (G * E) * W = W * (G * E) := baseJetA_commute_W m q v t
  have hpre : W * (G * E) * W = (W * W) * G * E := by
    calc
      W * (G * E) * W = W * ((G * E) * W) := by simp only [mul_assoc]
      _ = (W * W) * G * E := by rw [hcomm]; simp only [mul_assoc]
  rw [hpre]
  change (((W * W) * G) * baseJetE m q v) 0 (Fin.last m) = _
  rw [baseJetE_eq_shift_sum]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.sum_apply, Matrix.smul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have hdlt : d.val < m + 1 := by
    have hdq := d.isLt
    omega
  let dm : Fin (m + 1) := ⟨d.val, hdlt⟩
  rw [baseJet_mul_shift_corner m ((W * W) * G) dm]
  rw [baseJetW_square_G_top]
  rfl

/-- The actual frozen odd-Toeplitz jet polynomial of the exterior base
with one restored negative packet has the source's triangular finite
pencil formula. The bound is the source's present-section separation. -/
theorem baseJetPolynomial_formula (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) :
    oddJetPolynomial (baseJetSymbol m q v) m =
      Polynomial.X ^ m -
        2 * ∑ d : Fin q, Polynomial.C (v d) *
          (∑ k ∈ Finset.range (d.val + 1),
            Polynomial.C (((k + 1 : ℕ) : ℂ) * baseCoeff (d.val - k)) *
              Polynomial.X ^ k) := by
  apply Polynomial.funext
  intro t
  have hcalc : (oddJetPolynomial (baseJetSymbol m q v) m).eval t =
      t ^ m - 2 * ∑ d : Fin q, v d *
        (∑ k ∈ Finset.range (d.val + 1),
          (((k + 1 : ℕ) : ℂ) * baseCoeff (d.val - k)) * t ^ k) := by
    calc
      (oddJetPolynomial (baseJetSymbol m q v) m).eval t =
          ((oddC (baseJetSymbol m q v) m *
            oddB (baseJetSymbol m q v) m).charpoly).eval (t + 1) := by
        simp [oddJetPolynomial, oddQuotient]
      _ = (baseJetG m q v * baseJetG m q v -
            (t + 1) • baseUpperShift m).adjugate 0 (Fin.last m) := by
        rw [oddC_baseJetSymbol m q hq v, oddB_baseJetSymbol m q hq v]
        exact selected_charpoly_eq_pencil_adjugate m (baseJetG m q v) t
      _ = _ := by
        rw [baseJet_pencil_adjugate m q hq v t]
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        rw [baseJetW_corner, baseJetW_A_W_corner m q hq v t]
  simpa only [Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_finsetSum, Polynomial.eval_C] using hcalc

#assert_trust kernel baseJetPolynomial_formula
#print axioms baseJetPolynomial_formula

end NLA.Proofs.SP14
