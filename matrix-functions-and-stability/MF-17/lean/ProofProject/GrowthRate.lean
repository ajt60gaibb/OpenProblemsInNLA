import ProofProject.Definitions

/-!
# The growth clock and exponent

Elementary order facts needed to pass from the discrete lower-bound witnesses
to arbitrary large times. The logarithms always have positive arguments on the
nonnegative time axis.
-/

noncomputable section

namespace ProofProject

open Filter

lemma growthLog_argument_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < t + Real.exp (Real.exp 1) :=
  add_pos_of_nonneg_of_pos ht (Real.exp_pos _)

lemma growthLog_inner_one_le {t : ℝ} (ht : 0 ≤ t) :
    Real.exp 1 ≤ Real.log (t + Real.exp (Real.exp 1)) := by
  calc
    Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := (Real.log_exp _).symm
    _ ≤ Real.log (t + Real.exp (Real.exp 1)) :=
      Real.log_le_log (Real.exp_pos _) (le_add_of_nonneg_left ht)

lemma growthLog_inner_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < Real.log (t + Real.exp (Real.exp 1)) :=
  (Real.exp_pos 1).trans_le (growthLog_inner_one_le ht)

@[simp] lemma growthLog_zero : growthLog 0 = 1 := by
  simp [growthLog]

lemma strictMonoOn_growthLog : StrictMonoOn growthLog (Set.Ici 0) := by
  intro s hs t _ hst
  exact Real.log_lt_log (growthLog_inner_pos hs)
    (Real.log_lt_log (growthLog_argument_pos hs) (by linarith))

lemma growthLog_le_growthLog_iff {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    growthLog s ≤ growthLog t ↔ s ≤ t :=
  strictMonoOn_growthLog.le_iff_le hs ht

lemma growthLog_lt_growthLog_iff {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    growthLog s < growthLog t ↔ s < t :=
  strictMonoOn_growthLog.lt_iff_lt hs ht

lemma one_le_growthLog {t : ℝ} (ht : 0 ≤ t) : 1 ≤ growthLog t := by
  simpa using strictMonoOn_growthLog.monotoneOn (show (0 : ℝ) ∈ Set.Ici 0 by simp) ht ht

lemma growthLog_pos {t : ℝ} (ht : 0 ≤ t) : 0 < growthLog t :=
  zero_lt_one.trans_le (one_le_growthLog ht)

lemma tendsto_growthLog_atTop : Tendsto growthLog atTop atTop := by
  exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    (tendsto_atTop_add_const_right atTop (Real.exp (Real.exp 1)) tendsto_id))

lemma exists_lt_growthLog (b : ℝ) : ∃ t : ℝ, 0 ≤ t ∧ b < growthLog t := by
  refine ⟨Real.exp (Real.exp b), (Real.exp_pos _).le, ?_⟩
  unfold growthLog
  calc
    b = Real.log (Real.log (Real.exp (Real.exp b))) := by simp
    _ < Real.log (Real.log (Real.exp (Real.exp b) + Real.exp (Real.exp 1))) := by
      apply Real.log_lt_log
      · simpa using Real.exp_pos b
      · exact Real.log_lt_log (Real.exp_pos _)
          (lt_add_of_pos_right _ (Real.exp_pos _))

lemma growthLog_not_bddAbove : ¬ BddAbove (growthLog '' Set.Ici 0) := by
  rw [not_bddAbove_iff]
  intro b
  obtain ⟨t, ht, hbt⟩ := exists_lt_growthLog b
  exact ⟨growthLog t, ⟨t, ht, rfl⟩, hbt⟩

/-- Exact inversion of the clock, with all logarithmic side conditions explicit. -/
lemma growthLog_le_iff {t b : ℝ} (ht : 0 ≤ t) :
    growthLog t ≤ b ↔ t + Real.exp (Real.exp 1) ≤ Real.exp (Real.exp b) := by
  unfold growthLog
  rw [Real.log_le_iff_le_exp (growthLog_inner_pos ht),
    Real.log_le_iff_le_exp (growthLog_argument_pos ht)]

lemma le_growthLog_iff {t b : ℝ} (ht : 0 ≤ t) :
    b ≤ growthLog t ↔ Real.exp (Real.exp b) ≤ t + Real.exp (Real.exp 1) := by
  unfold growthLog
  rw [Real.le_log_iff_exp_le (growthLog_inner_pos ht),
    Real.le_log_iff_exp_le (growthLog_argument_pos ht)]

/-- A bound on a witness's clock is sufficient to place its time before `t`. -/
lemma time_le_of_growthLog_bounds {s t b : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hsb : growthLog s ≤ b) (hbt : b ≤ growthLog t) : s ≤ t :=
  (growthLog_le_growthLog_iff hs ht).mp (hsb.trans hbt)

@[simp] lemma growthExponent_one : growthExponent 1 = 0 := by
  simp [growthExponent]

lemma growthExponent_nonneg (M : ℝ) : 0 ≤ growthExponent M :=
  mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le) (Real.arccos_nonneg _)

lemma growthExponent_pos {M : ℝ} (hM : 1 < M) : 0 < growthExponent M := by
  have hM0 : 0 < M := zero_lt_one.trans hM
  exact mul_pos (div_pos (by norm_num) Real.pi_pos)
    (Real.arccos_pos.mpr ((div_lt_one hM0).mpr hM))

lemma growthExponent_lt_one {M : ℝ} (hM : 0 < M) : growthExponent M < 1 := by
  unfold growthExponent
  calc
    (2 / Real.pi) * Real.arccos (1 / M) < (2 / Real.pi) * (Real.pi / 2) :=
      mul_lt_mul_of_pos_left (Real.arccos_lt_pi_div_two.mpr (one_div_pos.mpr hM))
        (div_pos (by norm_num) Real.pi_pos)
    _ = 1 := by field_simp

lemma growthExponent_mem_Ioo {M : ℝ} (hM : 1 < M) :
    growthExponent M ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨growthExponent_pos hM, growthExponent_lt_one (zero_lt_one.trans hM)⟩

end ProofProject
