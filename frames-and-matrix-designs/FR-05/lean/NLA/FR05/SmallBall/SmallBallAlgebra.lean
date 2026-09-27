/-
Algebraic input to the small-ball analysis in Lemma 3.6.

This isolates the variance profile of the Gaussian term in the checked
Jacobian formula before the one-dimensional circle-sublevel estimate is
applied.
-/
import NLA.FR05.Planted.Jacobian
import NLA.FR05.Gaussian.GaussianTail

set_option autoImplicit false
open scoped BigOperators ComplexConjugate Matrix
noncomputable section

namespace NLA.FR05

/-- Squared Euclidean energy in the notation used for the variance profile. -/
def tailEnergy {n : ℕ} (x : Signal n) : ℝ :=
  ∑ j, Complex.normSq (x j)

theorem tailEnergy_eq_signalEnergy {n : ℕ} (x : Signal n) :
    tailEnergy x = signalEnergy x := rfl

/-- The conditional variance profile of the complex-Gaussian tail term in
equation (3.21). -/
def tailVarianceProfile {n : ℕ} (p q : Signal n) (φ : ℝ) : ℝ :=
  tailEnergy (p + Complex.exp ((φ : ℂ) * Complex.I) • q)

theorem normSq_phase (φ : ℝ) :
    Complex.normSq (Complex.exp ((φ : ℂ) * Complex.I)) = 1 := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem tailVarianceProfile_nonneg {n : ℕ} (p q : Signal n) (φ : ℝ) :
    0 ≤ tailVarianceProfile p q φ := by
  unfold tailVarianceProfile tailEnergy
  exact Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

/-- The exact cosine variance identity used in the tail-dominated branch of
Lemma 3.6. -/
theorem tailVarianceProfile_expand {n : ℕ} (p q : Signal n) (φ : ℝ) :
    tailVarianceProfile p q φ =
      tailEnergy p + tailEnergy q +
        2 * (Complex.exp ((φ : ℂ) * Complex.I) * (star p ⬝ᵥ q)).re := by
  classical
  unfold tailVarianceProfile tailEnergy
  change (∑ j, Complex.normSq (p j + Complex.exp ((φ : ℂ) * Complex.I) * q j)) =
    (∑ j, Complex.normSq (p j)) + (∑ j, Complex.normSq (q j)) +
      2 * (Complex.exp ((φ : ℂ) * Complex.I) * (star p ⬝ᵥ q)).re
  simp_rw [Complex.normSq_add, Complex.normSq_mul, normSq_phase]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  simp only [one_mul]
  rw [← Finset.mul_sum, ← Complex.re_sum]
  congr 1
  let e : ℂ := Complex.exp ((φ : ℂ) * Complex.I)
  change 2 * (∑ i, p i * star (e * q i)).re =
    2 * (e * (star p ⬝ᵥ q)).re
  congr 1
  calc
    (∑ i, p i * star (e * q i)).re =
        (star (∑ i, p i * star (e * q i))).re := by
          exact (Complex.conj_re _).symm
    _ = (∑ i, star (p i * star (e * q i))).re := by
          rw [star_sum]
    _ = (∑ i, e * (star (p i) * q i)).re := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          simp only [star_mul, star_star]
          ring
    _ = (e * (star p ⬝ᵥ q)).re := by
          rw [← Finset.mul_sum]
          congr 1

end NLA.FR05
