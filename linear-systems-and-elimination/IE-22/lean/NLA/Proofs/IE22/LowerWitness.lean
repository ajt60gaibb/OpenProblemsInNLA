import NLA.Proofs.IE22.NormalizedGaussianApprox
import NLA.Proofs.IE22.UniformFiniteSamples
import NLA.Proofs.IE22.GaussianTrimming

/-! Actual finite unit-row witnesses approaching the literal trimmed Gaussian
moment. The row sample and both extrema range over the original concrete model. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
namespace NLA.Proofs.IE22
open NLA.Statements.RowDeletion

/-- Actual unit-row matrices approach the sharp squared constant beyond
all prescribed dimension and aspect-ratio thresholds. -/
theorem near_sharp_unit_row_witness (θ a : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : 0 < a)
    (hquantile : GaussianQuantile θ a) :
    ∀ ε : ℝ, 0 < ε → ∀ N R : ℕ,
      ∃ n m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℝ,
        0 < n ∧ 0 < m ∧ N ≤ n ∧ R * n ≤ m ∧ UnitRows A ∧
          TrimmedMoment a - ε ≤ (n : ℝ) / (m : ℝ) * SubsingularSquared θ A := by
  classical
  intro ε hε N R
  obtain ⟨Npop, hpop⟩ := normalized_hinge_expectation_uniform (a ^ 2) (sq_nonneg a)
    (ε / 3) (by positivity)
  let n : ℕ := max (max N Npop) 1
  have hn : 0 < n := lt_of_lt_of_le (by decide : 0 < 1) (le_max_right _ _)
  have hN : N ≤ n := le_trans (le_max_left N Npop) (le_max_left _ _)
  have hnPop : Npop ≤ n := le_trans (le_max_right N Npop) (le_max_left _ _)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  obtain ⟨Mfloor, hMfloor⟩ := exists_nat_gt (3 * a ^ 2 / ε)
  let M0 := max (R * n) Mfloor
  obtain ⟨m, hm, hm0, ω, hsample⟩ := exists_uniform_sphere_sample n
    (stdGaussian (Euclid n)) (fun v g => hinge (a ^ 2) (normalizedObservation hn v g))
    (a ^ 2) (sq_nonneg a) (2 * (n : ℝ)).toNNReal
    (fun v _ => (measurable_normalized_hinge hn v _).aestronglyMeasurable)
    (fun v _ g => ⟨hinge_nonneg _ _, hinge_le (sq_nonneg a) _⟩)
    (fun g => normalized_hinge_direction_lipschitz hn g (a ^ 2))
    (ε / 3) (by positivity) M0
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hRm : R * n ≤ m := le_trans (le_max_left _ _) hm0
  have hmfloor : Mfloor ≤ m := le_trans (le_max_right _ _) hm0
  have hmLarge : 3 * a ^ 2 / ε < (m : ℝ) :=
    hMfloor.trans_le (by exact_mod_cast hmfloor)
  have hfloorloss : a ^ 2 ≤ (m : ℝ) * ε / 3 := by
    have hh := (div_lt_iff₀ hε).mp hmLarge
    nlinarith
  let A : Matrix (Fin m) (Fin n) ℝ := fun i j => normalizedGaussianRow hn (ω i) j
  have hA : UnitRows A := unit_rows_of_samples hn ω
  have hquant := gaussian_hinge_quantile_eq hθ0.le ha.le hquantile
  have hall : ∀ (S : Finset (Fin m)), S.card = RetainedCount θ m →
      ∀ x : Fin n → ℝ, UnitVector x →
        (m : ℝ) / (n : ℝ) * (TrimmedMoment a - ε) ≤
          ∑ i ∈ S, (RowValue A i x) ^ 2 := by
    intro S hS x hx
    let v : Euclid n := WithLp.toLp 2 x
    have hv2 : ‖v‖ ^ 2 = 1 := by
      rw [gaussian_norm_sq_eq_sum]
      exact hx
    have hv : ‖v‖ = 1 := by nlinarith [norm_nonneg v]
    have hvS : v ∈ Metric.sphere (0 : Euclid n) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hv
    have hp := hpop n hnPop hn v hv
    have hs := (hsample v hvS).le
    have hmean : (1 / (m : ℝ)) *
        (∑ i, hinge (a ^ 2) (normalizedObservation hn v (ω i))) ≤
        θ * a ^ 2 - TrimmedMoment a + 2 * ε / 3 := by
      rw [hquant] at hp
      have hp' := (abs_le.mp hp).2
      have hs' := (abs_le.mp hs).2
      linarith
    have hrow (i : Fin m) : inner ℝ v (normalizedGaussianRow hn (ω i)) = RowValue A i x := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, RowValue, v, A]
    have hobs (i : Fin m) : normalizedObservation hn v (ω i) ^ 2 =
        (n : ℝ) * (RowValue A i x) ^ 2 := by
      rw [normalizedObservation, mul_pow, Real.sq_sqrt hnR.le, hrow]
    have hsum : ∑ i, max (a ^ 2 - (n : ℝ) * (RowValue A i x) ^ 2) 0 ≤
        (m : ℝ) * (θ * a ^ 2 - TrimmedMoment a + 2 * ε / 3) := by
      have hle : (∑ i, hinge (a ^ 2) (normalizedObservation hn v (ω i))) ≤
          (m : ℝ) * (θ * a ^ 2 - TrimmedMoment a + 2 * ε / 3) := by
        have hmul := mul_le_mul_of_nonneg_left hmean hmR.le
        simpa only [← mul_assoc, mul_one_div_cancel hmne, one_mul] using hmul
      simpa only [hinge, hobs] using hle
    have hcard : θ * (m : ℝ) - 1 ≤ (S.card : ℝ) := by
      rw [hS]
      exact (Nat.sub_one_lt_floor (θ * (m : ℝ))).le
    have hcardmul := mul_le_mul_of_nonneg_right hcard (sq_nonneg a)
    have hdual := finite_trimming_dual_lower S
      (fun i => (n : ℝ) * (RowValue A i x) ^ 2) (a ^ 2)
    have hsumS : (∑ i ∈ S, (n : ℝ) * (RowValue A i x) ^ 2) =
        (n : ℝ) * ∑ i ∈ S, (RowValue A i x) ^ 2 := by rw [Finset.mul_sum]
    rw [hsumS] at hdual
    have henergy : (m : ℝ) * (TrimmedMoment a - ε) ≤
        (n : ℝ) * ∑ i ∈ S, (RowValue A i x) ^ 2 := by
      nlinarith [hsum, hcardmul, hdual, hfloorloss]
    calc
      (m : ℝ) / (n : ℝ) * (TrimmedMoment a - ε) =
          ((m : ℝ) * (TrimmedMoment a - ε)) / (n : ℝ) := by ring
      _ ≤ _ := (div_le_iff₀ hnR).mpr (by simpa only [mul_comm] using henergy)
  have hinf : (m : ℝ) / (n : ℝ) * (TrimmedMoment a - ε) ≤ SubsingularSquared θ A := by
    apply le_csInf (energy_values_nonempty hθ1.le hn A)
    rintro y ⟨S, hS, x, hx, rfl⟩
    exact hall S hS x hx
  refine ⟨n, m, A, hn, hm, hN, hRm, hA, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hinf (div_nonneg hnR.le hmR.le)
  have halg : (n : ℝ) / (m : ℝ) *
      ((m : ℝ) / (n : ℝ) * (TrimmedMoment a - ε)) = TrimmedMoment a - ε := by
    field_simp
  rwa [halg] at hmul

#assert_trust kernel near_sharp_unit_row_witness
#print axioms near_sharp_unit_row_witness
end NLA.Proofs.IE22
