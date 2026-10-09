import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Support

/-!
# Conjugation preserves the source amplitude hypotheses

The source amplitudes are complex. Changing the oscillatory sign by conjugation
therefore also conjugates the amplitude. Real differentiation commutes with
this operation, and the weighted derivative bounds and support are unchanged.
These lemmas do not assume a Fourier coefficient estimate.
-/

noncomputable section

namespace ProofProject

open scoped ContDiff

/-- Complex conjugation is real linear, so it preserves smoothness. -/
theorem sourceAmplitude_conj_contDiff {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (fun u => star (a u)) :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp ha

/-- Real differentiation commutes with amplitude conjugation. The identity
also respects Mathlib's derivative convention at nondifferentiable points. -/
theorem sourceAmplitude_deriv_conj (a : ℝ → ℂ) :
    deriv (fun u => star (a u)) = fun u => star (deriv a u) :=
  deriv.star'

theorem sourceAmplitude_deriv_twice_conj (a : ℝ → ℂ) :
    deriv (deriv (fun u => star (a u))) = fun u => star (deriv (deriv a) u) := by
  rw [sourceAmplitude_deriv_conj, sourceAmplitude_deriv_conj]

@[simp] theorem sourceAmplitude_conj_norm_deriv (a : ℝ → ℂ) (u : ℝ) :
    ‖deriv (fun v => star (a v)) u‖ = ‖deriv a u‖ := by
  rw [sourceAmplitude_deriv_conj]
  exact norm_star _

@[simp] theorem sourceAmplitude_conj_norm_deriv_twice (a : ℝ → ℂ) (u : ℝ) :
    ‖deriv (deriv (fun v => star (a v))) u‖ = ‖deriv (deriv a) u‖ := by
  rw [sourceAmplitude_deriv_twice_conj]
  exact norm_star _

/-- All three original weighted bounds hold with exactly the same constant. -/
theorem sourceAmplitude_conj_weighted_bounds {a : ℝ → ℂ} {A0 : ℝ}
    (h0 : ∀ u > 0, ‖a u‖ ≤ A0 * u ^ (-3 / 4 : ℝ))
    (h1 : ∀ u > 0, ‖deriv a u‖ ≤ A0 * u ^ (-3 / 4 - 1 : ℝ))
    (h2 : ∀ u > 0, ‖deriv (deriv a) u‖ ≤ A0 * u ^ (-3 / 4 - 2 : ℝ)) :
    (∀ u > 0, ‖star (a u)‖ ≤ A0 * u ^ (-3 / 4 : ℝ)) ∧
      (∀ u > 0, ‖deriv (fun v => star (a v)) u‖ ≤ A0 * u ^ (-3 / 4 - 1 : ℝ)) ∧
      (∀ u > 0, ‖deriv (deriv (fun v => star (a v))) u‖ ≤
        A0 * u ^ (-3 / 4 - 2 : ℝ)) := by
  simpa only [norm_star, sourceAmplitude_conj_norm_deriv,
    sourceAmplitude_conj_norm_deriv_twice] using And.intro h0 (And.intro h1 h2)

/-- Conjugation preserves exact support, not just a support upper bound. -/
theorem sourceAmplitude_conj_support (a : ℝ → ℂ) :
    Function.support (fun u => star (a u)) = Function.support a := by
  ext u
  simp only [Function.mem_support, star_ne_zero]

theorem sourceAmplitude_conj_tsupport (a : ℝ → ℂ) :
    tsupport (fun u => star (a u)) = tsupport a := by
  simp only [tsupport, sourceAmplitude_conj_support]

theorem sourceAmplitude_conj_hasCompactSupport {a : ℝ → ℂ} (ha : HasCompactSupport a) :
    HasCompactSupport (fun u => star (a u)) := by
  simpa only [HasCompactSupport, sourceAmplitude_conj_tsupport] using ha

theorem sourceAmplitude_conj_zero_outside {a : ℝ → ℂ} {s : Set ℝ}
    (ha : ∀ u, u ∉ s → a u = 0) : ∀ u, u ∉ s → star (a u) = 0 := by
  intro u hu
  rw [ha u hu, star_zero]

theorem sourceAmplitude_conj_zero_above {a : ℝ → ℂ} {b : ℝ}
    (ha : ∀ u, b < u → a u = 0) : ∀ u, b < u → star (a u) = 0 := by
  intro u hu
  rw [ha u hu, star_zero]

theorem sourceAmplitude_conj_zero_below {a : ℝ → ℂ} {b : ℝ}
    (ha : ∀ u, u < b → a u = 0) : ∀ u, u < b → star (a u) = 0 := by
  intro u hu
  rw [ha u hu, star_zero]

end ProofProject
