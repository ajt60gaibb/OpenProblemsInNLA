import NLA.Proofs.IE22.EnergyBounds
import NLA.Proofs.IE22.GaussianBasics

/-! Every normalized Gaussian outcome is an actual Euclidean unit row.
The zero outcome has a fixed unit fallback, so unit rows hold pointwise. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
namespace NLA.Proofs.IE22
open NLA.Statements.RowDeletion

def unitCoordinate {n : ℕ} (hn : 0 < n) : Euclid n :=
  PiLp.single 2 (⟨0, hn⟩ : Fin n) (1 : ℝ)

@[simp] theorem unitCoordinate_norm {n : ℕ} (hn : 0 < n) : ‖unitCoordinate hn‖ = 1 := by
  simp [unitCoordinate]

def normalizedGaussianRow {n : ℕ} (hn : 0 < n) (g : Euclid n) : Euclid n :=
  if g = 0 then unitCoordinate hn else ‖g‖⁻¹ • g

theorem normalizedGaussianRow_norm {n : ℕ} (hn : 0 < n) (g : Euclid n) :
    ‖normalizedGaussianRow hn g‖ = 1 := by
  by_cases hg : g = 0
  · simp [normalizedGaussianRow, hg]
  · simp only [normalizedGaussianRow, if_neg hg, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hg)

theorem normalizedGaussianRow_unitVector {n : ℕ} (hn : 0 < n) (g : Euclid n) :
    UnitVector (normalizedGaussianRow hn g).ofLp := by
  unfold UnitVector
  rw [← gaussian_norm_sq_eq_sum, normalizedGaussianRow_norm]
  norm_num

theorem measurable_normalizedGaussianRow {n : ℕ} (hn : 0 < n) :
    Measurable (normalizedGaussianRow hn) := by
  classical
  unfold normalizedGaussianRow
  exact Measurable.ite (isClosed_singleton.measurableSet)
    measurable_const (by fun_prop)

def normalizedObservation {n : ℕ} (hn : 0 < n) (v g : Euclid n) : ℝ :=
  Real.sqrt (n : ℝ) * inner ℝ v (normalizedGaussianRow hn g)

theorem normalizedObservation_sq {n : ℕ} (hn : 0 < n) (v g : Euclid n)
    (hg : g ≠ 0) :
    (normalizedObservation hn v g) ^ 2 =
      (n : ℝ) * (inner ℝ v g) ^ 2 / ‖g‖ ^ 2 := by
  simp only [normalizedObservation, normalizedGaussianRow, if_neg hg, inner_smul_right,
    mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  ring

theorem measurable_normalizedObservation {n : ℕ} (hn : 0 < n) (v : Euclid n) :
    Measurable (normalizedObservation hn v) := by
  exact measurable_const.mul ((innerSL ℝ v).continuous.measurable.comp
    (measurable_normalizedGaussianRow hn))

theorem measurable_normalized_hinge {n : ℕ} (hn : 0 < n) (v : Euclid n) (t : ℝ) :
    Measurable (fun g => hinge t (normalizedObservation hn v g)) := by
  unfold hinge
  exact (measurable_const.sub ((measurable_normalizedObservation hn v).pow_const 2)).max
    measurable_const

theorem memLp_normalized_hinge {n : ℕ} (hn : 0 < n) (v : Euclid n)
    {t : ℝ} (ht : 0 ≤ t) :
    MemLp (fun g => hinge t (normalizedObservation hn v g)) 2 (stdGaussian (Euclid n)) := by
  apply memLp_of_bounded
    (Filter.Eventually.of_forall (fun g =>
      (show hinge t (normalizedObservation hn v g) ∈ Set.Icc 0 t from
        ⟨hinge_nonneg _ _, hinge_le ht _⟩)))
    (measurable_normalized_hinge hn v t).aestronglyMeasurable

theorem unit_rows_of_samples {n m : ℕ} (hn : 0 < n) (ω : Fin m → Euclid n) :
    UnitRows (fun i j => normalizedGaussianRow hn (ω i) j) := by
  intro i
  exact normalizedGaussianRow_unitVector hn (ω i)

theorem hinge_diff_le_sq_diff (t x y : ℝ) :
    |hinge t x - hinge t y| ≤ |x ^ 2 - y ^ 2| := by
  have h := (LipschitzWith.id.max_const (0 : ℝ)).dist_le_mul
    (t - x ^ 2) (t - y ^ 2)
  have heq : (t - x ^ 2) - (t - y ^ 2) = -(x ^ 2 - y ^ 2) := by ring
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, heq, abs_neg, hinge, id_eq] using h

theorem normalized_hinge_direction_lipschitz {n : ℕ} (hn : 0 < n) (g : Euclid n)
    (t : ℝ) :
    LipschitzOnWith (2 * (n : ℝ)).toNNReal
      (fun v => hinge t (normalizedObservation hn v g)) (Metric.sphere 0 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  have hv1 : ‖v‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hv
  have hw1 : ‖w‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
  let u := normalizedGaussianRow hn g
  have hu : ‖u‖ = 1 := normalizedGaussianRow_norm hn g
  have hvu : |inner ℝ v u| ≤ 1 := by
    simpa only [Real.norm_eq_abs, hv1, hu, one_mul] using norm_inner_le_norm (𝕜 := ℝ) v u
  have hwu : |inner ℝ w u| ≤ 1 := by
    simpa only [Real.norm_eq_abs, hw1, hu, one_mul] using norm_inner_le_norm (𝕜 := ℝ) w u
  have hsum : |inner ℝ v u + inner ℝ w u| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith)
  have hdiff : |inner ℝ v u - inner ℝ w u| ≤ ‖v - w‖ := by
    rw [← inner_sub_left]
    simpa only [Real.norm_eq_abs, hu, mul_one] using norm_inner_le_norm (𝕜 := ℝ) (v - w) u
  have halg : (normalizedObservation hn v g) ^ 2 - (normalizedObservation hn w g) ^ 2 =
      (n : ℝ) * (inner ℝ v u - inner ℝ w u) * (inner ℝ v u + inner ℝ w u) := by
    simp only [normalizedObservation, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    dsimp [u]
    ring
  have hbound : |hinge t (normalizedObservation hn v g) -
      hinge t (normalizedObservation hn w g)| ≤ 2 * (n : ℝ) * ‖v - w‖ := by
    apply (hinge_diff_le_sq_diff _ _ _).trans
    rw [halg, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    calc
      _ ≤ ((n : ℝ) * ‖v - w‖) * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg n)) hsum
          (abs_nonneg _) (by positivity)
      _ = _ := by ring
  simpa [Real.dist_eq, Real.norm_eq_abs, dist_eq_norm,
    Real.toNNReal_of_nonneg (by positivity : 0 ≤ 2 * (n : ℝ))] using hbound

#assert_trust kernel normalizedGaussianRow_norm
#assert_trust kernel normalizedGaussianRow_unitVector
#assert_trust kernel measurable_normalizedGaussianRow
#assert_trust kernel normalizedObservation_sq
#assert_trust kernel measurable_normalizedObservation
#assert_trust kernel measurable_normalized_hinge
#assert_trust kernel memLp_normalized_hinge
#assert_trust kernel unit_rows_of_samples
#assert_trust kernel hinge_diff_le_sq_diff
#assert_trust kernel normalized_hinge_direction_lipschitz
#print axioms normalizedObservation_sq
#print axioms unit_rows_of_samples
#print axioms normalized_hinge_direction_lipschitz
end NLA.Proofs.IE22
