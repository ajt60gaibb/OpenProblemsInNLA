import ProofProject.FiniteCircleParseval
import ProofProject.LaurentCircleProduct
import ProofProject.FourierTailCoefficients

/-!
# Finite weighted positive-frequency projection

The vector polynomial uses negative frequencies. Finite Parseval then turns
nonnegative-frequency truncation of the scalar Laurent polynomial into the
existing coefficient tails. All integrals use normalized circle measure.
-/

noncomputable section

open MeasureTheory

namespace ProofProject

universe u

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

def reverseCircleWeight (v : Fin n → H) (z : AddCircle (1 : ℝ)) : ℝ :=
  ‖reverseCirclePolynomial v z‖ ^ 2

lemma reverseCircleWeight_nonneg (v : Fin n → H) (z : AddCircle (1 : ℝ)) :
    0 ≤ reverseCircleWeight v z := sq_nonneg _

lemma continuous_reverseCirclePolynomial (v : Fin n → H) :
    Continuous (reverseCirclePolynomial v) := by
  exact continuous_finsetSum _ fun j _ =>
    (fourier (T := (1 : ℝ)) (-(j.val : ℤ))).continuous.smul continuous_const

lemma continuous_reverseCircleWeight (v : Fin n → H) :
    Continuous (reverseCircleWeight v) :=
  (continuous_reverseCirclePolynomial v).norm.pow 2

lemma continuous_laurentCirclePolynomial (c : ℤ →₀ ℂ) :
    Continuous (laurentCirclePolynomial c) := by
  exact continuous_finsetSum _ fun m _ =>
    continuous_const.mul (fourier (T := (1 : ℝ)) m).continuous

lemma integrable_weightedCirclePolynomial (c : ℤ →₀ ℂ) (v : Fin n → H) :
    Integrable (fun z : AddCircle (1 : ℝ) =>
      ‖laurentCirclePolynomial c z‖ ^ 2 * reverseCircleWeight v z)
        AddCircle.haarAddCircle := by
  simpa only [MeasureTheory.integrableOn_univ, Pi.mul_def] using
    (((continuous_laurentCirclePolynomial c).norm.fun_pow 2).mul
      (continuous_reverseCircleWeight v)).continuousOn.integrableOn_compact
        (μ := AddCircle.haarAddCircle) isCompact_univ

lemma reverseCircleWeight_pos {v : Fin n → H} {K : ℝ}
    (h : HasSynthesisTailBound v K) (hv : ∃ j, v j ≠ 0)
    (z : AddCircle (1 : ℝ)) : 0 < reverseCircleWeight v z := by
  apply sq_pos_of_ne_zero
  apply norm_ne_zero_iff.mpr
  apply h.synthesis_ne_zero hv
  intro j
  have hnorm : ‖fourier (T := (1 : ℝ)) (-(j.val : ℤ)) z‖ = 1 :=
    finiteCircle_fourier_norm _ _
  exact norm_ne_zero_iff.mp (by rw [hnorm]; norm_num)

lemma reverseCircleWeight_at_zero (v : Fin n → H) :
    reverseCircleWeight v 0 = ‖finiteSynthesis v (fun _ => 1)‖ ^ 2 := by
  simp [reverseCircleWeight, reverseCirclePolynomial, finiteSynthesis]

/-- The mean of the weight is the original family's squared-norm sum. -/
lemma reverseCircleWeight_integral (v : Fin n → H) :
    (∫ z : AddCircle (1 : ℝ), reverseCircleWeight v z ∂AddCircle.haarAddCircle) =
      ∑ j, ‖v j‖ ^ 2 := by
  exact finiteCircleParseval_indexed (fun j : Fin n => -(j.val : ℤ))
    (by intro i j hij; dsimp only at hij; apply Fin.ext; omega) v

/-- Multiplying by one character turns the reverse-frequency polynomial into
an ordinary polynomial of degree at most `n-1`, preserving its circle norm. -/
lemma reverseCirclePolynomial_shift (v : Fin n → H) (z : AddCircle (1 : ℝ)) :
    fourier (T := (1 : ℝ)) ((n : ℤ) - 1) z • reverseCirclePolynomial v z =
      ∑ j : Fin n, fourier (T := (1 : ℝ)) ((n - 1 - j.val : ℕ) : ℤ) z • v j := by
  unfold reverseCirclePolynomial
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul, ← fourier_add]
  have hfreq : (n : ℤ) - 1 + -(j.val : ℤ) = ((n - 1 - j.val : ℕ) : ℤ) := by omega
  rw [hfreq]

lemma reverseCircleWeight_eq_forward_norm_sq (v : Fin n → H)
    (z : AddCircle (1 : ℝ)) :
    reverseCircleWeight v z =
      ‖∑ j : Fin n, fourier (T := (1 : ℝ)) ((n - 1 - j.val : ℕ) : ℤ) z • v j‖ ^ 2 := by
  rw [← reverseCirclePolynomial_shift, norm_smul, finiteCircle_fourier_norm, one_mul]
  rfl

/-- Exact weighted Parseval over any common finite frequency set. -/
theorem weightedCircle_parseval (c : ℤ →₀ ℂ) (v : Fin n → H)
    (s : Finset ℤ) (hs : laurentProductFrequencies c n ⊆ s) :
    (∫ z : AddCircle (1 : ℝ), ‖laurentCirclePolynomial c z‖ ^ 2 * reverseCircleWeight v z
      ∂AddCircle.haarAddCircle) = ∑ q ∈ s, ‖laurentProductCoefficient c v q‖ ^ 2 := by
  calc
    _ = ∫ z : AddCircle (1 : ℝ),
        ‖laurentCirclePolynomial c z • reverseCirclePolynomial v z‖ ^ 2
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        dsimp only
        rw [norm_smul, mul_pow, reverseCircleWeight]
    _ = ∫ z : AddCircle (1 : ℝ),
        ‖∑ q ∈ s, fourier q z • laurentProductCoefficient c v q‖ ^ 2
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        dsimp only
        rw [laurentCirclePolynomial_smul_reverse c v s hs z]
    _ = _ := finiteCircleParseval s (laurentProductCoefficient c v)

/-- The source finite transference inequality. Scalar nonnegative-frequency
truncation has weighted squared norm at most `K²` times the original norm.
It follows from the actual coefficient-tail bound, with no Hardy-space or
infinite Parseval premise. -/
theorem weightedCircle_nonnegative_projection_le {v : Fin n → H} {K : ℝ}
    (h : HasSynthesisTailBound v K) (c : ℤ →₀ ℂ) :
    (∫ z : AddCircle (1 : ℝ),
      ‖laurentCirclePolynomial (c.filter (fun m => 0 ≤ m)) z‖ ^ 2 * reverseCircleWeight v z
        ∂AddCircle.haarAddCircle) ≤
      K ^ 2 * ∫ z : AddCircle (1 : ℝ),
        ‖laurentCirclePolynomial c z‖ ^ 2 * reverseCircleWeight v z
          ∂AddCircle.haarAddCircle := by
  rw [weightedCircle_parseval (c.filter (fun m => 0 ≤ m)) v
      (laurentProductFrequencies c n) (laurentProductFrequencies_filter_subset c n _),
    weightedCircle_parseval c v (laurentProductFrequencies c n) (Finset.Subset.refl _)]
  simpa only [laurentProductCoefficient, Finsupp.filter_apply] using
    fourierTail_energy_le h (laurentProductFrequencies c n) c

end ProofProject
