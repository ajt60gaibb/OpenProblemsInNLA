import NLA.Proofs.IE22.GaussianUpperBounds
import NLA.Proofs.IE22.GaussianNormBounds

/-! A simultaneous good realization of the actual standard Gaussian vector.
The three failure probabilities are obtained from its energy expectation,
norm-square variance, and the variance of the finite family of trimming duals. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace NLA.Proofs.IE22
open NLA.Statements.RowDeletion

theorem gaussian_row_energy_mean_le {m d : ℕ} (b : Fin m → Euclid d)
    (hb : ∀ i, ‖b i‖ ^ 2 ≤ 1) :
    (∫ g, ∑ i, (inner ℝ (b i) g) ^ 2 ∂stdGaussian (Euclid d)) ≤ (m : ℝ) := by
  have hLp (i : Fin m) : MemLp (fun g : Euclid d => inner ℝ (b i) g) 2
      (stdGaussian (Euclid d)) := (gaussian_inner_pair_law (b i) (b i)).fst.memLp_two
  have hInt (i : Fin m) : Integrable (fun g : Euclid d => (inner ℝ (b i) g)^2)
      (stdGaussian (Euclid d)) := (memLp_two_iff_integrable_sq (by fun_prop)).mp (hLp i)
  have hmean (i : Fin m) :
      (∫ g : Euclid d, (inner ℝ (b i) g)^2 ∂stdGaussian (Euclid d)) = ‖b i‖^2 := by
    have h := variance_eq_sub (hLp i)
    rw [gaussian_inner_mean, gaussian_inner_variance] at h
    simpa only [Pi.pow_apply, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using h.symm
  rw [integral_finsetSum _ (fun i _ => hInt i)]
  simp_rw [hmean]
  calc
    ∑ i, ‖b i‖^2 ≤ ∑ _i : Fin m, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hb i)
    _ = (m : ℝ) := by simp

theorem gaussian_row_energy_markov {m d : ℕ} (hm : 0 < m)
    (b : Fin m → Euclid d) (hb : ∀ i, ‖b i‖^2 ≤ 1) :
    stdGaussian (Euclid d) {g | 4*(m : ℝ) < ∑ i, (inner ℝ (b i) g)^2} ≤
      ENNReal.ofReal (1/4 : ℝ) := by
  let μ := stdGaussian (Euclid d)
  have hInt : Integrable (fun g : Euclid d => ∑ i, (inner ℝ (b i) g)^2) μ := by
    apply integrable_finsetSum
    intro i _
    exact (memLp_two_iff_integrable_sq (by fun_prop)).mp
      (gaussian_inner_pair_law (b i) (b i)).fst.memLp_two
  have h := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun g : Euclid d => ∑ i, (inner ℝ (b i) g)^2)
    (ae_of_all _ (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) hInt (4*(m : ℝ))
  have hmean := gaussian_row_energy_mean_le b hb
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hreal : μ.real {g | 4*(m : ℝ) ≤ ∑ i, (inner ℝ (b i) g)^2} ≤ 1/4 := by
    nlinarith
  have hbound : μ {g | 4*(m : ℝ) ≤ ∑ i, (inner ℝ (b i) g)^2} ≤
      ENNReal.ofReal (1/4 : ℝ) := by
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by norm_num)).mpr hreal
  apply (measure_mono (t := {g | 4*(m : ℝ) ≤ ∑ i, (inner ℝ (b i) g)^2}) ?_).trans hbound
  intro g hg
  change 4*(m : ℝ) < ∑ i, (inner ℝ (b i) g)^2 at hg
  change 4*(m : ℝ) ≤ ∑ i, (inner ℝ (b i) g)^2
  exact hg.le

theorem exists_good_gaussian {m d r : ℕ} (hm : 0 < m) (hd : 0 < d)
    {θ a : ℝ} (hθ0 : 0 ≤ θ) (ha : 0 ≤ a) (hq : GaussianQuantile θ a)
    (b : Fin m → Euclid d) (hb : ∀ i, ‖b i‖^2 ≤ 1)
    (hgram : (∑ i, ∑ j, |inner ℝ (b i) (b j)|) ≤
      (m : ℝ)^2/Real.sqrt (r+1 : ℕ))
    (δ : ℝ) (hδ : 0 < δ) (_hδ1 : δ < 1)
    (L : ℝ) (hL : 0 ≤ L) (F : Finset ℝ)
    (hF : ∀ t ∈ F, 0 ≤ t ∧ t ≤ L)
    (hprob : (1/4 : ℝ) + (F.card : ℝ)*(4*L/(Real.sqrt (r+1 : ℕ)*δ^2)) +
      normalSquareVariance/((d : ℝ)*δ^2) < 1) :
    ∃ g : Euclid d,
      (1-δ)*(d : ℝ) ≤ ‖g‖^2 ∧
      (∑ i, (inner ℝ (b i) g)^2) ≤ 4*(m : ℝ) ∧
      ∀ t ∈ F, gaussianTrimmingDual θ b t g ≤ TrimmedMoment a + δ := by
  classical
  let μ := stdGaussian (Euclid d)
  let E : Set (Euclid d) := {g | 4*(m : ℝ) < ∑ i, (inner ℝ (b i) g)^2}
  let Q : Set (Euclid d) := {g | ‖g‖^2 < (1-δ)*(d : ℝ)}
  let B : ℝ → Set (Euclid d) := fun t =>
    {g | TrimmedMoment a + δ < gaussianTrimmingDual θ b t g}
  let p : ℝ := 4*L/(Real.sqrt (r+1 : ℕ)*δ^2)
  let q : ℝ := normalSquareVariance/((d : ℝ)*δ^2)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt (r+1 : ℕ) := by positivity
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg normalSquareVariance_nonneg (by positivity)
  have hE : μ E ≤ ENNReal.ofReal (1/4 : ℝ) := gaussian_row_energy_markov hm b hb
  have hQ : μ Q ≤ ENNReal.ofReal q := by
    apply (measure_mono (t := {g : Euclid d | δ ≤ |‖g‖^2/(d : ℝ)-1|}) ?_).trans
      (gaussian_relative_norm_square_chebyshev hd δ hδ)
    intro g hg
    change ‖g‖^2 < (1-δ)*(d : ℝ) at hg
    have hdiv : ‖g‖^2/(d : ℝ) < 1-δ := (div_lt_iff₀ hdR).mpr hg
    have habs := neg_le_abs (‖g‖^2/(d : ℝ)-1)
    change δ ≤ |‖g‖^2/(d : ℝ)-1|
    linarith
  have hB (t : ℝ) (ht : t ∈ F) : μ (B t) ≤ ENNReal.ofReal p := by
    have hmean := gaussianTrimmingDual_mean_le hm hθ0 ha hq b hb (hF t ht).1
    have htail := meas_ge_le_variance_div_sq
      (gaussianTrimmingDual_memLp θ b (hF t ht).1) hδ
    have hsubset : B t ⊆ {g : Euclid d | δ ≤
        |gaussianTrimmingDual θ b t g - ∫ x, gaussianTrimmingDual θ b t x ∂μ|} := by
      intro g hg
      change TrimmedMoment a + δ < gaussianTrimmingDual θ b t g at hg
      have habs := le_abs_self
        (gaussianTrimmingDual θ b t g - ∫ x, gaussianTrimmingDual θ b t x ∂μ)
      change δ ≤ |gaussianTrimmingDual θ b t g - ∫ x, gaussianTrimmingDual θ b t x ∂μ|
      linarith
    refine (measure_mono hsubset).trans (htail.trans (ENNReal.ofReal_le_ofReal ?_))
    calc
      Var[gaussianTrimmingDual θ b t; μ] / δ^2 ≤
          (4*t/Real.sqrt (r+1 : ℕ))/δ^2 :=
        div_le_div_of_nonneg_right (gaussianTrimmingDual_variance_le hm θ b hgram (hF t ht).1)
          (sq_nonneg δ)
      _ ≤ p := by
        dsimp [p]
        rw [div_div]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hF t ht).2 (by norm_num))
          (by positivity)
  have hU : μ (E ∪ (⋃ t ∈ F, B t) ∪ Q) < 1 := by
    calc
      μ (E ∪ (⋃ t ∈ F, B t) ∪ Q) ≤ μ E + μ (⋃ t ∈ F, B t) + μ Q :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal (1/4 : ℝ) + (∑ t ∈ F, ENNReal.ofReal p) + ENNReal.ofReal q :=
        add_le_add (add_le_add hE ((measure_biUnion_finset_le F B).trans
          (Finset.sum_le_sum (fun t ht => hB t ht)))) hQ
      _ = ENNReal.ofReal ((1/4 : ℝ) + (F.card : ℝ)*p + q) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hp)]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_add (by positivity) hq0,
          ENNReal.ofReal_add (by norm_num) (mul_nonneg (Nat.cast_nonneg _) hp)]
      _ < 1 := ENNReal.ofReal_lt_one.mpr hprob
  have hne : (E ∪ (⋃ t ∈ F, B t) ∪ Q) ≠ univ := by
    intro heq
    rw [heq, measure_univ] at hU
    exact (lt_irrefl _ hU)
  obtain ⟨g, hg⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  have hgQ : g ∉ Q := fun h => hg (Or.inr h)
  have hgE : g ∉ E := fun h => hg (Or.inl (Or.inl h))
  refine ⟨g, le_of_not_gt hgQ, le_of_not_gt hgE, fun t ht => ?_⟩
  apply le_of_not_gt
  intro h
  exact hg (Or.inl (Or.inr (mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨ht, h⟩⟩)))

#assert_trust kernel gaussian_row_energy_mean_le
#assert_trust kernel gaussian_row_energy_markov
#assert_trust kernel exists_good_gaussian
#print axioms gaussian_row_energy_mean_le
#print axioms gaussian_row_energy_markov
#print axioms exists_good_gaussian
end NLA.Proofs.IE22
