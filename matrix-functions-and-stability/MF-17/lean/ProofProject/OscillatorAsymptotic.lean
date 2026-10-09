import ProofProject.OscillatorEnergy
import ProofProject.DerivativeTailLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Oscillatory asymptotics of the inverse-square perturbed oscillator

The two rotating coefficients have integrable inverse-square derivatives.
Their actual limits give a sine/cosine approximation with error `O(1/r)`.
-/

noncomputable section

open Set

namespace ProofProject

def oscillatorCosCoefficient (v p : ℝ → ℝ) (r : ℝ) : ℝ :=
  v r * Real.cos r - p r * Real.sin r

def oscillatorSinCoefficient (v p : ℝ → ℝ) (r : ℝ) : ℝ :=
  v r * Real.sin r + p r * Real.cos r

theorem oscillatorCosCoefficient_hasDerivAt {v p : ℝ → ℝ} {r : ℝ}
    (hv : HasDerivAt v (p r) r)
    (hp : HasDerivAt p (-v r + 3 * v r / (4 * r ^ 2)) r) :
    HasDerivAt (oscillatorCosCoefficient v p)
      (-(3 / 4 : ℝ) * v r * Real.sin r / r ^ 2) r := by
  convert! (hv.mul (Real.hasDerivAt_cos r)).sub (hp.mul (Real.hasDerivAt_sin r)) using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem oscillatorSinCoefficient_hasDerivAt {v p : ℝ → ℝ} {r : ℝ}
    (hv : HasDerivAt v (p r) r)
    (hp : HasDerivAt p (-v r + 3 * v r / (4 * r ^ 2)) r) :
    HasDerivAt (oscillatorSinCoefficient v p)
      ((3 / 4 : ℝ) * v r * Real.cos r / r ^ 2) r := by
  convert! (hv.mul (Real.hasDerivAt_sin r)).add (hp.mul (Real.hasDerivAt_cos r)) using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem oscillator_rotating_identity (v p : ℝ → ℝ) (r : ℝ) :
    v r = oscillatorCosCoefficient v p r * Real.cos r +
      oscillatorSinCoefficient v p r * Real.sin r := by
  dsimp [oscillatorCosCoefficient, oscillatorSinCoefficient]
  calc
    _ = v r * (Real.sin r ^ 2 + Real.cos r ^ 2) := by rw [Real.sin_sq_add_cos_sq]; ring
    _ = _ := by ring

private theorem oscillator_rotating_deriv_bound {V r x z : ℝ} (_hV : 0 ≤ V)
    (hr : 0 < r) (hx : |x| ≤ V) (hz : |z| ≤ 1) :
    |(3 / 4 : ℝ) * x * z / r ^ 2| ≤ ((3 / 4 : ℝ) * V) * r ^ (-2 : ℝ) := by
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4),
    abs_of_pos (sq_pos_of_pos hr)]
  have hm : |x| * |z| ≤ V := (mul_le_of_le_one_right (abs_nonneg _) hz).trans hx
  calc
    _ = ((3 / 4 : ℝ) * (|x| * |z|)) / r ^ 2 := by ring
    _ ≤ ((3 / 4 : ℝ) * V) / r ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num)) (sq_nonneg _)
    _ = _ := by rw [Real.rpow_neg (le_of_lt hr)]; norm_num [div_eq_mul_inv]

/-- The leading coefficients are actual limits of the rotating coordinates;
no assertion about their exact values or nonvanishing is required. -/
theorem exists_oscillator_asymptotic {v p : ℝ → ℝ}
    (hv : ∀ r, 1 ≤ r → HasDerivAt v (p r) r)
    (hp : ∀ r, 1 ≤ r → HasDerivAt p (-v r + 3 * v r / (4 * r ^ 2)) r) :
    ∃ A₀ A₁ C : ℝ, 0 ≤ C ∧ ∀ r, 1 ≤ r →
      |v r - (A₀ * Real.cos r + A₁ * Real.sin r)| ≤ C / r := by
  obtain ⟨V, hV, hbound⟩ := exists_oscillator_uniform_bound hv hp
  have hvc : ContinuousOn v (Ici 1) := fun r hr => (hv r hr).continuousAt.continuousWithinAt
  let g₀ := fun r => -(3 / 4 : ℝ) * v r * Real.sin r / r ^ 2
  let g₁ := fun r => (3 / 4 : ℝ) * v r * Real.cos r / r ^ 2
  have hg₀ : ContinuousOn g₀ (Ici 1) := by
    apply (continuousOn_const.mul hvc |>.mul Real.continuous_sin.continuousOn).div
      (continuous_id.pow 2).continuousOn
    intro r hr
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le zero_lt_one hr))
  have hg₁ : ContinuousOn g₁ (Ici 1) := by
    apply (continuousOn_const.mul hvc |>.mul Real.continuous_cos.continuousOn).div
      (continuous_id.pow 2).continuousOn
    intro r hr
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le zero_lt_one hr))
  obtain ⟨A₀, _, hA₀⟩ := exists_limit_of_deriv_le_inv_sq (by positivity : 0 ≤ (3 / 4 : ℝ) * V)
    (fun r hr => oscillatorCosCoefficient_hasDerivAt (hv r hr) (hp r hr)) hg₀
    (fun r hr => by
      rw [neg_mul, neg_mul, neg_div, abs_neg]
      exact oscillator_rotating_deriv_bound hV (by linarith) (hbound r hr).1
        (Real.abs_sin_le_one r))
  obtain ⟨A₁, _, hA₁⟩ := exists_limit_of_deriv_le_inv_sq (by positivity : 0 ≤ (3 / 4 : ℝ) * V)
    (fun r hr => oscillatorSinCoefficient_hasDerivAt (hv r hr) (hp r hr)) hg₁
    (fun r hr => oscillator_rotating_deriv_bound hV (by linarith) (hbound r hr).1
      (Real.abs_cos_le_one r))
  refine ⟨A₀, A₁, (3 / 2 : ℝ) * V, by positivity, ?_⟩
  intro r hr
  have heq : v r - (A₀ * Real.cos r + A₁ * Real.sin r) =
      (oscillatorCosCoefficient v p r - A₀) * Real.cos r +
        (oscillatorSinCoefficient v p r - A₁) * Real.sin r := by
    conv_lhs => rw [oscillator_rotating_identity v p r]
    ring
  rw [heq]
  calc
    _ ≤ |(oscillatorCosCoefficient v p r - A₀) * Real.cos r| +
        |(oscillatorSinCoefficient v p r - A₁) * Real.sin r| := abs_add_le _ _
    _ ≤ |oscillatorCosCoefficient v p r - A₀| + |oscillatorSinCoefficient v p r - A₁| := by
      simp only [abs_mul]
      exact add_le_add
        (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one r))
        (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one r))
    _ ≤ ((3 / 4 : ℝ) * V) / r + ((3 / 4 : ℝ) * V) / r := add_le_add (hA₀ r hr) (hA₁ r hr)
    _ = _ := by ring

end ProofProject
