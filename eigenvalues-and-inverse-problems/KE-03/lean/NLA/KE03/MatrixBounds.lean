import NLA.KE03.Probability

/-! Euclidean norm estimates for the integer random start and shifted powers. -/

noncomputable section
open scoped BigOperators

namespace NLA.KE03

@[simp] theorem act_one {n : ℕ} : act (1 : Mat n) = 1 := map_one _
@[simp] theorem act_mul {n : ℕ} (A B : Mat n) : act (A * B) = act A * act B :=
  map_mul Matrix.toEuclideanCLM A B
@[simp] theorem act_add {n : ℕ} (A B : Mat n) : act (A + B) = act A + act B :=
  map_add Matrix.toEuclideanCLM A B
@[simp] theorem act_smul {n : ℕ} (z : ℂ) (A : Mat n) : act (z • A) = z • act A :=
  map_smul Matrix.toEuclideanCLM z A
@[simp] theorem act_pow {n : ℕ} (A : Mat n) (m : ℕ) : act (A ^ m) = act A ^ m :=
  map_pow Matrix.toEuclideanCLM A m

theorem act_apply {n : ℕ} (A : Mat n) (v : Vec n) (i : Fin n) :
    (act A v) i = ∑ j, A i j * v j := rfl

theorem opNorm_nonneg {n : ℕ} (A : Mat n) : 0 ≤ opNorm A := norm_nonneg _

theorem norm_act_le {n : ℕ} (A : Mat n) (v : Vec n) :
    ‖act A v‖ ≤ opNorm A * ‖v‖ := (act A).le_opNorm v

open scoped Matrix.Norms.L2Operator in
theorem opNorm_diagonal {n : ℕ} (d : Fin n → ℂ) :
    opNorm (Matrix.diagonal d) = ‖d‖ := by
  change ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (Matrix.diagonal d)‖ = ‖d‖
  rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]

theorem entry_norm_le_opNorm {n : ℕ} (A : Mat n) (i j : Fin n) :
    ‖A i j‖ ≤ opNorm A := by
  let e : Vec n := PiLp.single 2 j 1
  have he : ‖e‖ = 1 := by simp [e]
  have ha : (act A e) i = A i j := by
    simp [act_apply, e, PiLp.single_apply, Finset.sum_ite_eq']
  rw [← ha]
  exact (PiLp.norm_apply_le (act A e) i).trans (by simpa [he] using norm_act_le A e)

theorem seedVector_norm_le {n : ℕ} (hn : 0 < n) (seed : Seed n) :
    ‖seedVector seed‖ ≤ n * gridSize n := by
  have hsq : ‖seedVector seed‖ ^ 2 ≤ (n : ℝ) * (gridSize n : ℝ) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc _ ≤ ∑ _i : Fin n, (gridSize n : ℝ) ^ 2 := by
           apply Finset.sum_le_sum
           intro i _
           change ‖((seed i).val : ℂ)‖ ^ 2 ≤ _
           rw [Complex.norm_natCast]
           exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast (seed i).isLt.le) _
         _ = _ := by simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hg0 : (0 : ℝ) ≤ gridSize n := by positivity
  have hnn : (n : ℝ) ≤ n ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hnn (sq_nonneg (gridSize n : ℝ))
  nlinarith [norm_nonneg (seedVector seed), mul_nonneg hn0 hg0]

theorem diagonalization_shift_pow {n : ℕ} (A V W : Mat n) (lam : Fin n → ℂ)
    (hVW : V * W = 1) (hWV : W * V = 1) (hA : A = V * Matrix.diagonal lam * W)
    (s : ℂ) (m : ℕ) :
    (A + s • 1) ^ m = V * Matrix.diagonal (fun i => (lam i + s) ^ m) * W := by
  have hs : A + s • 1 = V * Matrix.diagonal (fun i => lam i + s) * W := by
    rw [hA, show Matrix.diagonal (fun i => lam i + s) =
      Matrix.diagonal lam + s • (1 : Mat n) by
        ext i j
        by_cases hij : i = j <;> simp [hij]]
    simp [Matrix.mul_add, Matrix.add_mul, hVW]
  rw [hs]
  induction m with
  | zero => simpa using hVW.symm
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc W V, hWV, Matrix.one_mul]
    rw [← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _),
      Matrix.diagonal_mul_diagonal]
    congr 2

theorem eigenvalue_iff_diagonal {n : ℕ} (A V W : Mat n) (lam : Fin n → ℂ)
    (hVW : V * W = 1) (hWV : W * V = 1) (hA : A = V * Matrix.diagonal lam * W)
    (μ : ℂ) : Eigenvalue A μ ↔ ∃ i, lam i = μ := by
  have hWA : W * A = Matrix.diagonal lam * W := by
    rw [hA]
    simp [← Matrix.mul_assoc, hWV]
  have hAV : A * V = V * Matrix.diagonal lam := by
    rw [hA]
    simp [Matrix.mul_assoc, hWV]
  constructor
  · rintro ⟨v, hv, he⟩
    have hwv : act W v ≠ 0 := by
      intro h
      apply hv
      have hh := congrArg (fun x => act V x) h
      simpa [← mul_apply_eq_comp, ← act_mul, hVW] using hh
    obtain ⟨i, hi⟩ : ∃ i, (act W v) i ≠ 0 := by
      by_contra! h
      apply hwv
      ext i
      exact h i
    have hh : act (Matrix.diagonal lam) (act W v) = μ • act W v := by
      calc _ = act W (act A v) := by
             simp only [← mul_apply_eq_comp, ← act_mul, hWA]
           _ = _ := by rw [he, map_smul]
    have hc : lam i * (act W v) i = μ * (act W v) i := by
      simpa [act_apply, Matrix.diagonal_apply] using congrArg (fun x : Vec n => x i) hh
    exact ⟨i, mul_right_cancel₀ hi hc⟩
  · rintro ⟨i, rfl⟩
    let e : Vec n := PiLp.single 2 i 1
    have he : e ≠ 0 := by
      intro h
      have := congrArg (fun x : Vec n => x i) h
      simp [e] at this
    have hdiag : act (Matrix.diagonal lam) e = lam i • e := by
      ext j
      simp [act_apply, Matrix.diagonal_apply, e, PiLp.single_apply]
      split_ifs <;> simp_all
    refine ⟨act V e, ?_, ?_⟩
    · intro h
      apply he
      have hh := congrArg (fun x => act W x) h
      simpa [← mul_apply_eq_comp, ← act_mul, hWV] using hh
    · calc act A (act V e) = act V (act (Matrix.diagonal lam) e) := by
             simp only [← mul_apply_eq_comp, ← act_mul, hAV]
           _ = _ := by rw [hdiag, map_smul]

theorem radius_eq_diagonal_norm {n : ℕ} (hn : 0 < n) (A V W : Mat n)
    (lam : Fin n → ℂ) (hVW : V * W = 1) (hWV : W * V = 1)
    (hA : A = V * Matrix.diagonal lam * W) : radius A = ‖lam‖ := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hs : {r : ℝ | ∃ μ : ℂ, Eigenvalue A μ ∧ r = ‖μ‖} =
      Set.range (fun i => ‖lam i‖) := by
    ext r
    simp only [Set.mem_ofPred_eq, eigenvalue_iff_diagonal A V W lam hVW hWV hA,
      Set.mem_range]
    aesop
  rw [radius, hs]
  exact (IsGreatest.pi_norm lam).isLUB.csSup_eq (Set.range_nonempty _)

theorem inverse_row_lower {n : ℕ} (V W : Mat n) (hWV : W * V = 1) (i : Fin n) :
    1 ≤ n * ‖W i‖ * opNorm V := by
  have he : (∑ j, W i j * V j i) = 1 := by
    simpa [Matrix.mul_apply] using congrArg (fun M : Mat n => M i i) hWV
  calc
    (1 : ℝ) = ‖∑ j, W i j * V j i‖ := by rw [he]; simp
    _ ≤ ∑ j, ‖W i j * V j i‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, ‖W i‖ * opNorm V := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (norm_le_pi_norm (W i) j) (entry_norm_le_opNorm V j i)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

theorem diagonal_action_bounds {n : ℕ} (hn : 0 < n) (V W : Mat n)
    (_hVW : V * W = 1) (hWV : W * V = 1) (K : ℝ) (hK : 1 ≤ K)
    (hcond : opNorm V * opNorm W ≤ K) (seed : Seed n) (hgood : GoodSeed W seed)
    (d : Fin n → ℂ) :
    ‖d‖ ≤ distortion n K * ‖act (V * Matrix.diagonal d * W) (seedVector seed)‖ ∧
      ‖act (V * Matrix.diagonal d * W) (seedVector seed)‖ ≤ distortion n K * ‖d‖ := by
  let b := seedVector seed
  let y := act (V * Matrix.diagonal d * W) b
  have hv0 := opNorm_nonneg V
  have hw0 := opNorm_nonneg W
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hN1 : (1 : ℝ) ≤ gridSize n := by exact_mod_cast gridSize_pos n
  have hF : 2 * n * K ≤ distortion n K := by
    dsimp [distortion]
    nlinarith [mul_nonneg hn0 (show 0 ≤ K by linarith)]
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by dsimp [distortion]; positivity)).2
    intro i
    have hy : act W y = act (Matrix.diagonal d) (act W b) := by
      dsimp [y]
      simp only [← mul_apply_eq_comp, ← act_mul]
      congr 1
      simp [← Matrix.mul_assoc, hWV]
    have hcoord : ‖d i‖ * ‖(act W b) i‖ ≤ opNorm W * ‖y‖ := by
      rw [← norm_mul]
      have he : d i * (act W b) i = (act W y) i := by
        rw [hy]
        simp [act_apply, Matrix.diagonal_apply]
      rw [he]
      exact (PiLp.norm_apply_le (act W y) i).trans (norm_act_le W y)
    have hg := hgood i
    change ‖W i‖ ≤ 2 * ‖(act W b) i‖ at hg
    have hr := inverse_row_lower V W hWV i
    have hdi := norm_nonneg (d i)
    have hy0 := norm_nonneg y
    have haux : ‖d i‖ * ‖W i‖ ≤ 2 * opNorm W * ‖y‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hg hdi]
    have hmul := mul_le_mul_of_nonneg_left haux (mul_nonneg hn0 hv0)
    have hmul2 := mul_le_mul_of_nonneg_left hr hdi
    have hmul3 := mul_le_mul_of_nonneg_left hcond
      (show 0 ≤ 2 * (n : ℝ) * ‖y‖ by positivity)
    have hsmall : ‖d i‖ ≤ (2 * n * K) * ‖y‖ := by nlinarith
    exact hsmall.trans (mul_le_mul_of_nonneg_right hF hy0)
  · have he : y = act V (act (Matrix.diagonal d) (act W b)) := by
      simp [y, act_mul, mul_apply_eq_comp]
    have hfirst : ‖y‖ ≤ (opNorm V * opNorm W) * ‖d‖ * ‖b‖ := by
      rw [he]
      calc _ ≤ opNorm V * ‖act (Matrix.diagonal d) (act W b)‖ := norm_act_le _ _
           _ ≤ opNorm V * (‖d‖ * ‖act W b‖) := by
             gcongr
             simpa [opNorm_diagonal] using norm_act_le (Matrix.diagonal d) (act W b)
           _ ≤ opNorm V * (‖d‖ * (opNorm W * ‖b‖)) := by
             gcongr
             exact norm_act_le _ _
           _ = _ := by ring
    have hb := seedVector_norm_le hn seed
    change ‖b‖ ≤ n * gridSize n at hb
    have hsecond : ‖y‖ ≤ K * ‖d‖ * (n * gridSize n) := by
      calc _ ≤ (opNorm V * opNorm W) * ‖d‖ * ‖b‖ := hfirst
           _ ≤ K * ‖d‖ * (n * gridSize n) := by gcongr
    change ‖y‖ ≤ distortion n K * ‖d‖
    dsimp [distortion]
    nlinarith [mul_nonneg (show 0 ≤ K by linarith) (norm_nonneg d),
      mul_nonneg hn0 (show 0 ≤ (gridSize n : ℝ) by positivity)]

theorem pi_norm_power {n : ℕ} (hn : 0 < n) (d : Fin n → ℂ) (m : ℕ) :
    ‖fun i => d i ^ m‖ = ‖d‖ ^ m := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm d i) _
  · obtain ⟨i, hi⟩ := (IsGreatest.pi_norm d).1
    change ‖d i‖ = ‖d‖ at hi
    rw [← hi, ← norm_pow]
    exact norm_le_pi_norm (fun i => d i ^ m) i

/-- One good start controls every shifted power, with no further randomness. -/
theorem shifted_power_bounds {n : ℕ} (hn : 0 < n) (A V W : Mat n)
    (lam : Fin n → ℂ) (hVW : V * W = 1) (hWV : W * V = 1)
    (hA : A = V * Matrix.diagonal lam * W) (K : ℝ) (hK : 1 ≤ K)
    (hcond : opNorm V * opNorm W ≤ K) (seed : Seed n) (hgood : GoodSeed W seed)
    (s : ℂ) (m : ℕ) :
    ‖fun i => lam i + s‖ ^ m ≤
        distortion n K * ‖act ((A + s • 1) ^ m) (seedVector seed)‖ ∧
      ‖act ((A + s • 1) ^ m) (seedVector seed)‖ ≤
        distortion n K * ‖fun i => lam i + s‖ ^ m := by
  rw [diagonalization_shift_pow A V W lam hVW hWV hA]
  simpa only [pi_norm_power hn] using
    diagonal_action_bounds hn V W hVW hWV K hK hcond seed hgood
      (fun i => (lam i + s) ^ m)

end NLA.KE03
