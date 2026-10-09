import NLA.TR07.IdealKernel
import NLA.TR07.IdealEstimator
import NLA.TR07.CovarianceFilter
import NLA.TR07.FiniteVectorAverage

/-! Dimension-independent reconstruction success for the finite ideal experiment. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace NLA.TR07
open Law Matrix
variable {α : Type*} [Fintype α] {k s : ℕ}

/-- The finite transition realizes the regularized covariance action exactly. -/
theorem idealKernel_mean (p : Law α) (u : α → Vec k)
    (hu : ∀ a, SignedVector s (u a)) (hk : 0 < k) (hs : 0 < s)
    (x : SignedState α) :
    (idealKernel p u hu hk hs x).mean (stateVector u) =
      (transitionMatrix p u s).toEuclideanLin (stateVector u x) := by
  ext j
  rw [idealKernel_mean_entry]
  simp only [transitionMatrix, Matrix.toLpLin_apply, smul_mulVec,
    Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, WithLp.ofLp_toLp, Matrix.mul_diagonal]

private theorem matrix_action_mul (A B : Mat k k) :
    (A*B).toEuclideanLin = A.toEuclideanLin * B.toEuclideanLin := by
  ext v i
  simp [Matrix.toLpLin_apply, mulVec_mulVec]

private theorem matrix_action_one : (1 : Mat k k).toEuclideanLin = 1 := by
  ext v i
  simp

private theorem matrix_action_pow (A : Mat k k) (L : ℕ) :
    (A^L).toEuclideanLin = A.toEuclideanLin^L := by
  induction L with
  | zero => rw [pow_zero, pow_zero]; exact matrix_action_one
  | succ L ih => rw [pow_succ, matrix_action_mul, ih, pow_succ]

theorem ideal_trajectory_mean (p : Law α) (u : α → Vec k)
    (hu : ∀ a, SignedVector s (u a)) (hk : 0 < k) (hs : 0 < s) (L : ℕ) (a : α) :
    (Law.paths (idealKernel p u hu hk hs) L (some (false,a))).mean
      (trajectoryEstimator (stateVector u) L) =
      u a - ((1-transitionMatrix p u s)^L).toEuclideanLin (u a) := by
  rw [trajectoryEstimator_mean _ _ _ (idealKernel_mean p u hu hk hs)]
  simp only [stateVector_pos]
  rw [matrix_action_pow, map_sub, matrix_action_one]

omit [Fintype α] in
theorem ideal_estimator_norm_sq_le (u : α → Vec k) (hu : ∀ a, SignedVector s (u a))
    (L : ℕ) (z : Fin L → SignedState α) :
    ‖trajectoryEstimator (stateVector u) L z‖^2 ≤ (s:ℝ) * ((2:ℝ)^L-1)^2 := by
  have hs0 : (0:ℝ) ≤ s := Nat.cast_nonneg _
  have hu' (a : SignedState α) : ‖stateVector u a‖ ≤ Real.sqrt s := by
    have h := stateVector_norm_sq_le u hu a
    nlinarith [Real.sq_sqrt hs0, Real.sqrt_nonneg (s:ℝ), norm_nonneg (stateVector u a)]
  have h := trajectoryEstimator_norm_le (stateVector u) hu' L z
  have hpow : 0 ≤ (2:ℝ)^L-1 := sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  calc
    _ ≤ (((2:ℝ)^L-1)*Real.sqrt s)^2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hpow (Real.sqrt_nonneg _))).mpr h
    _ = _ := by rw [mul_pow, Real.sq_sqrt hs0]; ring

/-- Choose a center and `b` independent length-`L` ideal trajectories from that center. -/
def idealExperiment (p : Law α) (u : α → Vec k)
    (hu : ∀ a, SignedVector s (u a)) (hk : 0 < k) (hs : 0 < s) (L b : ℕ) :
    Law (α × (Fin b → Fin L → SignedState α)) :=
  p.bind (fun a => ((Law.paths (idealKernel p u hu hk hs) L (some (false,a))).iid b).map
    (fun z => (a,z)))

def reconstruction (u : α → Vec k) (L b : ℕ) (z : Fin b → Fin L → SignedState α) : Vec k :=
  Law.average b (trajectoryEstimator (stateVector u) L) z

theorem ideal_reconstruction_error (p : Law α) (u : α → Vec k)
    (hu : ∀ a, SignedVector s (u a)) (hk : 0 < k) (hs : 0 < s)
    (L b : ℕ) (hb : 0 < b) :
    (idealExperiment p u hu hk hs L b).expect (fun z => ‖u z.1 - reconstruction u L b z.2‖^2) ≤
      2*(s:ℝ)^2/(2*L+1) + (s:ℝ)*((2:ℝ)^L-1)^2/b := by
  unfold idealExperiment reconstruction
  rw [expect_bind]
  simp_rw [expect_map]
  calc
    _ ≤ p.expect (fun a => ‖((1-transitionMatrix p u s)^L).toEuclideanLin (u a)‖^2 +
        (s:ℝ)*((2:ℝ)^L-1)^2/b) := by
      apply p.expect_mono
      intro a
      have h := squared_error_iid_average_le
        (Law.paths (idealKernel p u hu hk hs) L (some (false,a))) b hb
        (trajectoryEstimator (stateVector u) L) (u a)
      rw [ideal_trajectory_mean p u hu hk hs L a, sub_sub_cancel] at h
      exact h.trans (add_le_add_right (div_le_div_of_nonneg_right
        ((Law.paths (idealKernel p u hu hk hs) L (some (false,a))).expect_le_const
          (ideal_estimator_norm_sq_le u hu L)) (Nat.cast_nonneg b)) _)
    _ = p.expect (fun a => ‖((1-transitionMatrix p u s)^L).toEuclideanLin (u a)‖^2) +
        (s:ℝ)*((2:ℝ)^L-1)^2/b := by rw [expect_add, expect_const]
    _ ≤ _ := add_le_add_left (sparse_filter_bound p u hu hk hs L) _

/-- The number and lengths of trajectories depend only on sparsity and target error. -/
theorem exists_estimator_parameters (s : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L b : ℕ, 0 < L ∧ 0 < b ∧
      2*(s:ℝ)^2/(2*L+1) + (s:ℝ)*((2:ℝ)^L-1)^2/b ≤ ε^2/4 := by
  have heps : 0 < ε^2/8 := by positivity
  have aux (c : ℝ) : ∃ b : ℕ, 0 < b ∧ c/(b:ℝ) ≤ ε^2/8 := by
    obtain ⟨b,hb⟩ := exists_nat_gt (max (c/(ε^2/8)) 0)
    have hb0 : (0:ℝ) < b := lt_of_le_of_lt (le_max_right _ _) hb
    refine ⟨b, by exact_mod_cast hb0, ?_⟩
    apply (div_le_iff₀ hb0).mpr
    have hc := (div_lt_iff₀ heps).mp (lt_of_le_of_lt (le_max_left _ _) hb)
    linarith
  obtain ⟨L,hL,hLb⟩ := aux (2*(s:ℝ)^2)
  obtain ⟨b,hb,hbb⟩ := aux ((s:ℝ)*((2:ℝ)^L-1)^2)
  refine ⟨L,b,hL,hb,?_⟩
  have hL0 : (0:ℝ) < L := by exact_mod_cast hL
  have hfilter : 2*(s:ℝ)^2/(2*L+1) ≤ 2*(s:ℝ)^2/L := by
    apply div_le_div_of_nonneg_left (by positivity) hL0
    linarith
  linarith

theorem ideal_success_probability (p : Law α) (u : α → Vec k)
    (hu : ∀ a, SignedVector s (u a)) (hk : 0 < k) (hs : 0 < s)
    (L b : ℕ) (hb : 0 < b) {ε : ℝ} (hε : 0 < ε)
    (hbudget : 2*(s:ℝ)^2/(2*L+1) + (s:ℝ)*((2:ℝ)^L-1)^2/b ≤ ε^2/4) :
    (3:ℝ)/4 ≤ (idealExperiment p u hu hk hs L b).prob
      (fun z => ‖u z.1 - reconstruction u L b z.2‖ ≤ ε) := by
  let q := idealExperiment p u hu hk hs L b
  let err (z : α × (Fin b → Fin L → SignedState α)) := ‖u z.1 - reconstruction u L b z.2‖
  have hE : q.expect (fun z => err z^2) ≤ ε^2/4 :=
    (ideal_reconstruction_error p u hu hk hs L b hb).trans hbudget
  have hM := q.markov (fun z => err z^2) (fun z => sq_nonneg _) (sq_pos_of_pos hε)
  have hbad : q.prob (fun z => ¬ err z ≤ ε) ≤ (1:ℝ)/4 := by
    apply le_trans (q.prob_mono ?_) (hM.trans ?_)
    · intro z hz
      push Not at hz
      have he : 0 ≤ err z := norm_nonneg _
      nlinarith
    · apply (div_le_iff₀ (sq_pos_of_pos hε)).mpr
      linarith
  rw [prob_not] at hbad
  change (3:ℝ)/4 ≤ q.prob (fun z => err z ≤ ε)
  linarith

end NLA.TR07
