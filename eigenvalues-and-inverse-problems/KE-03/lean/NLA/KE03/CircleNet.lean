import NLA.KE03.Search

noncomputable section

namespace NLA.KE03

@[simp] theorem circlePoint_re (t : ℝ) : (circlePoint t).re = (1 - t ^ 2) / (1 + t ^ 2) := by
  simp only [circlePoint, ← Complex.ofReal_div, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

@[simp] theorem circlePoint_im (t : ℝ) : (circlePoint t).im = (2 * t) / (1 + t ^ 2) := by
  simp only [circlePoint, ← Complex.ofReal_div, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem circlePoint_norm (t : ℝ) : ‖circlePoint t‖ = 1 := by
  have hd : 1 + t ^ 2 ≠ 0 := by positivity
  have hs : ‖circlePoint t‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, circlePoint_re, circlePoint_im]
    field_simp
    ring
  nlinarith [norm_nonneg (circlePoint t)]

theorem circlePoint_dist_sq (s t : ℝ) :
    ‖circlePoint s - circlePoint t‖ ^ 2 =
      4 * (s - t) ^ 2 / ((1 + s ^ 2) * (1 + t ^ 2)) := by
  have hs : 1 + s ^ 2 ≠ 0 := by positivity
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, circlePoint_re, circlePoint_im]
  field_simp
  ring

theorem circlePoint_dist_le (s t : ℝ) :
    ‖circlePoint s - circlePoint t‖ ≤ 2 * |s - t| := by
  have hd : 1 ≤ (1 + s ^ 2) * (1 + t ^ 2) := by nlinarith [sq_nonneg s, sq_nonneg t]
  have hh := div_le_self (show 0 ≤ 4 * (s - t) ^ 2 by positivity) hd
  rw [← circlePoint_dist_sq] at hh
  nlinarith [sq_abs (s - t), norm_nonneg (circlePoint s - circlePoint t), abs_nonneg (s - t)]

theorem circlePoint_surj_right {u : ℂ} (hu : ‖u‖ = 1) (hre : 0 ≤ u.re) :
    ∃ t : ℝ, -1 ≤ t ∧ t ≤ 1 ∧ circlePoint t = u := by
  have hsq : u.re ^ 2 + u.im ^ 2 = 1 := by
    calc
      _ = Complex.normSq u := by simp [Complex.normSq_apply, pow_two]
      _ = ‖u‖ ^ 2 := Complex.normSq_eq_norm_sq u
      _ = 1 := by rw [hu]; norm_num
  have hd : 0 < 1 + u.re := by linarith
  have him : |u.im| ≤ 1 + u.re := by
    have hi : u.im ^ 2 ≤ (1 + u.re) ^ 2 := by nlinarith
    nlinarith [sq_abs u.im, abs_nonneg u.im]
  refine ⟨u.im / (1 + u.re), ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hd).mpr
    have := (abs_le.mp him).1
    linarith
  · apply (div_le_iff₀ hd).mpr
    have := (abs_le.mp him).2
    linarith
  · apply Complex.ext
    · rw [circlePoint_re]
      field_simp
      nlinarith
    · rw [circlePoint_im]
      field_simp
      nlinarith [congrArg (fun x : ℝ => u.im * x) hsq]

theorem circleMesh_unit {q : ℕ} {u : ℂ} (hu : u ∈ circleMesh q) : ‖u‖ = 1 := by
  simp only [circleMesh, List.mem_cons, List.mem_flatMap] at hu
  rcases hu with rfl | ⟨j, _, hj⟩
  · simp
  · simp only [List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact circlePoint_norm _
    · simpa using circlePoint_norm (-1 + 2 * (j : ℝ) / (q : ℝ))

/-- A rational mesh point within one mesh interval, including both endpoints. -/
theorem real_mesh_near {q : ℕ} (hq : 0 < q) {t : ℝ} (ht : -1 ≤ t) (ht' : t ≤ 1) :
    ∃ j : ℕ, j ≤ q ∧ |t - (-1 + 2 * (j : ℝ) / (q : ℝ))| ≤ 2 / q := by
  let x : ℝ := (t + 1) * q / 2
  have hx : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg q)) (by norm_num)
  have hxq : x ≤ q := by dsimp [x]; nlinarith [show (0 : ℝ) ≤ q by positivity]
  refine ⟨⌊x⌋₊, ?_, ?_⟩
  · exact_mod_cast (Nat.floor_le hx).trans hxq
  · have hfloor := Nat.floor_le hx
    have hlt := Nat.lt_floor_add_one x
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hid : (t - (-1 + 2 * (⌊x⌋₊ : ℝ) / (q : ℝ))) * q =
        2 * (x - (⌊x⌋₊ : ℝ)) := by
      dsimp [x]
      field_simp
      ring
    have hnonneg : 0 ≤ t - (-1 + 2 * (⌊x⌋₊ : ℝ) / (q : ℝ)) := by
      nlinarith
    rw [abs_of_nonneg hnonneg]
    apply (le_div_iff₀ hqR).mpr
    nlinarith

theorem circleMesh_near {q : ℕ} (hq : 0 < q) {ε : ℝ} (_hε : 0 < ε)
    (hqe : 32 ≤ ε * q) {u : ℂ} (hu : ‖u‖ = 1) :
    ∃ v ∈ circleMesh q, ‖u - v‖ ≤ ε / 8 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hbound : 4 / (q : ℝ) ≤ ε / 8 := by
    apply (div_le_iff₀ hqR).mpr
    nlinarith
  have aux : ∀ w : ℂ, ‖w‖ = 1 → 0 ≤ w.re →
      ∃ j : ℕ, j ≤ q ∧ ‖w - circlePoint (-1 + 2 * (j : ℝ) / q)‖ ≤ ε / 8 := by
    intro w hw hwr
    obtain ⟨t, ht, ht', heq⟩ := circlePoint_surj_right hw hwr
    obtain ⟨j, hj, hjt⟩ := real_mesh_near hq ht ht'
    refine ⟨j, hj, ?_⟩
    rw [← heq]
    calc
      _ ≤ 2 * |t - (-1 + 2 * (j : ℝ) / q)| := circlePoint_dist_le _ _
      _ ≤ 2 * (2 / (q : ℝ)) := mul_le_mul_of_nonneg_left hjt (by norm_num)
      _ = 4 / (q : ℝ) := by ring
      _ ≤ ε / 8 := hbound
  by_cases hre : 0 ≤ u.re
  · obtain ⟨j, hj, hdist⟩ := aux u hu hre
    refine ⟨circlePoint (-1 + 2 * (j : ℝ) / q), ?_, hdist⟩
    simp only [circleMesh, List.mem_cons, List.mem_flatMap]
    right
    refine ⟨(j : ℝ), ?_, by simp⟩
    exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr (by omega), by simp⟩
  · obtain ⟨j, hj, hdist⟩ := aux (-u) (by simpa) (by simpa using (le_of_not_ge hre))
    refine ⟨-circlePoint (-1 + 2 * (j : ℝ) / q), ?_, ?_⟩
    · simp only [circleMesh, List.mem_cons, List.mem_flatMap]
      right
      refine ⟨(j : ℝ), ?_, by simp⟩
      exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr (by omega), by simp⟩
    · have he : -u - circlePoint (-1 + 2 * (j : ℝ) / q) =
          -(u - -circlePoint (-1 + 2 * (j : ℝ) / q)) := by abel
      rw [he, norm_neg] at hdist
      exact hdist

end NLA.KE03
