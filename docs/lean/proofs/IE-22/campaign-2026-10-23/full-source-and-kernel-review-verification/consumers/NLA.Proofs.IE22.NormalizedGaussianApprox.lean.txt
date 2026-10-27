import NLA.Proofs.IE22.NormalizedGaussianRows
import NLA.Proofs.IE22.GaussianNormBounds
import NLA.Proofs.IE22.GaussianCovariance

/-! Uniform-in-direction expectation approximation using actual Gaussian norm
moments. No independence of the Gaussian radius and direction is required. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
namespace NLA.Proofs.IE22

theorem normalized_hinge_expectation_error {n : ℕ} (hn : 0 < n)
    (v : Euclid n) (hv : ‖v‖ = 1) (t : ℝ) (ht : 0 ≤ t) :
    |(∫ g : Euclid n, hinge t (normalizedObservation hn v g) ∂stdGaussian (Euclid n)) -
      ∫ z : ℝ, hinge t z ∂gaussianReal 0 1| ≤
      2 * Real.sqrt (normalFourthMoment * normalSquareVariance / (n : ℝ)) +
        4 * t * normalSquareVariance / (n : ℝ) := by
  classical
  let P := stdGaussian (Euclid n)
  let Z : Euclid n → ℝ := fun g => inner ℝ v g
  let q : Euclid n → ℝ := fun g => ‖g‖ ^ 2 / (n : ℝ)
  let D : Euclid n → ℝ := fun g => q g - 1
  let bad : Set (Euclid n) := {g | q g < 1 / 2}
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hmap : P.map Z = gaussianReal 0 1 := gaussian_unit_inner_law v hv
  have hpres : MeasurePreserving Z P (gaussianReal 0 1) := ⟨by fun_prop, hmap⟩
  have hZ2 : MemLp (fun g => Z g ^ 2) 2 P := normal_square_memLp.comp_measurePreserving hpres
  have hD : MemLp D 2 P := gaussian_relative_norm_square_memLp n
  have hDabs : MemLp (fun g => |D g|) 2 P := by
    simpa only [Real.norm_eq_abs] using hD.norm
  have hM4 : (∫ g, (Z g ^ 2) ^ 2 ∂P) = normalFourthMoment := by
    calc
      _ = ∫ z : ℝ, z ^ 4 ∂P.map Z := by
        rw [integral_map (by fun_prop) (by fun_prop)]
        congr 1
        ext g
        ring
      _ = normalFourthMoment := by rw [hmap]; rfl
  have hD2 : (∫ g, |D g| ^ 2 ∂P) = normalSquareVariance / (n : ℝ) := by
    simp_rw [sq_abs]
    exact gaussian_relative_norm_square_second_moment hn
  have hprodint : Integrable (fun g => Z g ^ 2 * |D g|) P := hZ2.integrable_mul hDabs
  have hprod : (∫ g, Z g ^ 2 * |D g| ∂P) ≤
      Real.sqrt (normalFourthMoment * normalSquareVariance / (n : ℝ)) := by
    have h := integral_mul_sq_le (fun g => Z g ^ 2) (fun g => |D g|) hZ2 hDabs
    rw [hM4, hD2] at h
    have hc : 0 ≤ normalFourthMoment * normalSquareVariance / (n : ℝ) :=
      div_nonneg (mul_nonneg normalFourthMoment_nonneg normalSquareVariance_nonneg) hnR.le
    have hs := Real.sq_sqrt hc
    have hn0 : 0 ≤ ∫ g, Z g ^ 2 * |D g| ∂P := integral_nonneg fun _ => by positivity
    have hroot := Real.sqrt_nonneg (normalFourthMoment * normalSquareVariance / (n : ℝ))
    have halg : normalFourthMoment * (normalSquareVariance / (n : ℝ)) =
        normalFourthMoment * normalSquareVariance / (n : ℝ) := by ring
    rw [halg] at h
    nlinarith
  have hbadmeas : MeasurableSet bad := by
    change MeasurableSet {g : Euclid n | ‖g‖ ^ 2 / (n : ℝ) < 1 / 2}
    exact measurableSet_lt (by fun_prop) measurable_const
  have hbad : P.real bad ≤ 4 * normalSquareVariance / (n : ℝ) := by
    exact ENNReal.toReal_le_of_le_ofReal
      (div_nonneg (mul_nonneg (by norm_num) normalSquareVariance_nonneg) hnR.le)
      (gaussian_small_norm_probability hn)
  have hindint : Integrable (bad.indicator (fun _ => t)) P :=
    (integrable_const t).indicator hbadmeas
  have hind : (∫ g, bad.indicator (fun _ => t) g ∂P) ≤
      4 * t * normalSquareVariance / (n : ℝ) := by
    rw [integral_indicator_const t hbadmeas, smul_eq_mul]
    calc
      P.real bad * t ≤ (4 * normalSquareVariance / (n : ℝ)) * t :=
        mul_le_mul_of_nonneg_right hbad ht
      _ = _ := by ring
  have hpt (g : Euclid n) :
      |hinge t (normalizedObservation hn v g) - hinge t (Z g)| ≤
        2 * (Z g ^ 2 * |D g|) + bad.indicator (fun _ => t) g := by
    by_cases hb : g ∈ bad
    · rw [indicator_of_mem hb]
      have hu := hinge_le ht (normalizedObservation hn v g)
      have hl := hinge_nonneg t (normalizedObservation hn v g)
      have hu' := hinge_le ht (Z g)
      have hl' := hinge_nonneg t (Z g)
      have hdiff : |hinge t (normalizedObservation hn v g) - hinge t (Z g)| ≤ t :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      exact hdiff.trans (le_add_of_nonneg_left (by positivity))
    · rw [indicator_of_notMem hb, add_zero]
      have hq : 1 / 2 ≤ q g := le_of_not_gt hb
      have hqpos : 0 < q g := lt_of_lt_of_le (by norm_num) hq
      have hg : g ≠ 0 := by
        intro hz
        simp [q, hz] at hqpos
      have hnormne : ‖g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
      have hobsq : normalizedObservation hn v g ^ 2 * q g = Z g ^ 2 := by
        rw [normalizedObservation_sq hn v g hg]
        dsimp [q, Z]
        field_simp
      have hid : (normalizedObservation hn v g ^ 2 - Z g ^ 2) * q g =
          Z g ^ 2 * (1 - q g) := by nlinarith [hobsq]
      have habs := congrArg abs hid
      rw [abs_mul, abs_of_pos hqpos, abs_mul, abs_of_nonneg (sq_nonneg (Z g)),
        abs_sub_comm (1 : ℝ) (q g)] at habs
      have hdiff : |normalizedObservation hn v g ^ 2 - Z g ^ 2| ≤
          2 * (Z g ^ 2 * |D g|) := by
        change _ ≤ 2 * (Z g ^ 2 * |q g - 1|)
        nlinarith [abs_nonneg (normalizedObservation hn v g ^ 2 - Z g ^ 2)]
      have hh := abs_max_sub_max_le_abs
        (t - normalizedObservation hn v g ^ 2) (t - Z g ^ 2) 0
      have heq : |(t - normalizedObservation hn v g ^ 2) - (t - Z g ^ 2)| =
          |normalizedObservation hn v g ^ 2 - Z g ^ 2| := by
        rw [show (t - normalizedObservation hn v g ^ 2) - (t - Z g ^ 2) =
          -(normalizedObservation hn v g ^ 2 - Z g ^ 2) by ring, abs_neg]
      exact (hh.trans_eq heq).trans hdiff
  have hNint := (memLp_normalized_hinge hn v ht).integrable (by norm_num)
  have hZhingeLp : MemLp (fun g => hinge t (Z g)) 2 P := by
    apply memLp_of_bounded (Filter.Eventually.of_forall (fun g =>
      (show hinge t (Z g) ∈ Icc 0 t from ⟨hinge_nonneg _ _, hinge_le ht _⟩)))
    exact (by unfold hinge Z; fun_prop : AEStronglyMeasurable (fun g => hinge t (Z g)) P)
  have hZint := hZhingeLp.integrable (by norm_num)
  have hscalar : (∫ g, hinge t (Z g) ∂P) = ∫ z : ℝ, hinge t z ∂gaussianReal 0 1 := by
    rw [← hmap, integral_map (by fun_prop) (by unfold hinge; fun_prop)]
  rw [← hscalar, ← integral_sub hNint hZint]
  calc
    |∫ g, hinge t (normalizedObservation hn v g) - hinge t (Z g) ∂P| ≤
        ∫ g, |hinge t (normalizedObservation hn v g) - hinge t (Z g)| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun g => hinge t (normalizedObservation hn v g) - hinge t (Z g))
    _ ≤ ∫ g, 2 * (Z g ^ 2 * |D g|) + bad.indicator (fun _ => t) g ∂P := by
      apply integral_mono
        (by simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hNint.sub hZint).norm)
        ((hprodint.const_mul 2).add hindint)
      exact hpt
    _ = 2 * (∫ g, Z g ^ 2 * |D g| ∂P) + ∫ g, bad.indicator (fun _ => t) g ∂P := by
      rw [integral_add (hprodint.const_mul 2) hindint, integral_const_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hprod (by norm_num)) hind


/-- The expectation error vanishes uniformly over every actual unit direction. -/
theorem normalized_hinge_expectation_uniform (t : ℝ) (ht : 0 ≤ t)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ hn : 0 < n, ∀ v : Euclid n, ‖v‖ = 1 →
      |(∫ g : Euclid n, hinge t (normalizedObservation hn v g) ∂stdGaussian (Euclid n)) -
        ∫ z : ℝ, hinge t z ∂gaussianReal 0 1| ≤ ε := by
  let A := normalFourthMoment * normalSquareVariance
  let B := 4 * t * normalSquareVariance
  have hA : 0 ≤ A := mul_nonneg normalFourthMoment_nonneg normalSquareVariance_nonneg
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (by norm_num) ht) normalSquareVariance_nonneg
  obtain ⟨N, hN⟩ := exists_nat_gt (max (16 * A / ε ^ 2) (2 * B / ε))
  refine ⟨N, fun n hnN hn v hv => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hnN
  have hlarge : max (16 * A / ε ^ 2) (2 * B / ε) < (n : ℝ) := hN.trans_le hNn
  have hA' : 16 * A < (n : ℝ) * ε ^ 2 :=
    (div_lt_iff₀ (sq_pos_of_pos hε)).mp ((le_max_left _ _).trans_lt hlarge)
  have hB' : 2 * B < (n : ℝ) * ε :=
    (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hlarge)
  have hAdiv : A / (n : ℝ) ≤ ε ^ 2 / 16 := by
    apply (div_le_iff₀ hnR).2
    nlinarith
  have hBdiv : B / (n : ℝ) ≤ ε / 2 := by
    apply (div_le_iff₀ hnR).2
    nlinarith
  have hsqrt : Real.sqrt (A / (n : ℝ)) ≤ ε / 4 := by
    have hs := Real.sq_sqrt (div_nonneg hA hnR.le)
    have hs0 := Real.sqrt_nonneg (A / (n : ℝ))
    nlinarith
  have hmain := normalized_hinge_expectation_error hn v hv t ht
  change _ ≤ 2 * Real.sqrt (A / (n : ℝ)) + B / (n : ℝ) at hmain
  exact hmain.trans (by linarith)

#assert_trust kernel normalized_hinge_expectation_error
#assert_trust kernel normalized_hinge_expectation_uniform
#print axioms normalized_hinge_expectation_error
#print axioms normalized_hinge_expectation_uniform
end NLA.Proofs.IE22
