import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Polynomial approximation of a zero-free polynomial reciprocal

A polynomial with no zeros on the closed unit disk has no zeros on a slightly
larger closed disk. The reciprocal therefore has a Cauchy power series there.
Its scalar multilinear partial sums are evaluations of actual polynomials,
and converge uniformly on the closed unit disk.
-/

noncomputable section

open Filter Metric Polynomial Set
open scoped Topology NNReal ENNReal

namespace ProofProject

/-- The ordinary polynomial underlying a scalar multilinear partial sum. -/
def scalarSeriesPolynomial (p : FormalMultilinearSeries ℂ ℂ ℂ) (N : ℕ) :
    Polynomial ℂ :=
  ∑ k ∈ Finset.range N, monomial k (p k (fun _ => 1))

theorem scalarSeriesPolynomial_eval (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (N : ℕ) (z : ℂ) :
    (scalarSeriesPolynomial p N).eval z = p.partialSum N z := by
  simp only [scalarSeriesPolynomial, eval_finsetSum, eval_monomial,
    FormalMultilinearSeries.partialSum]
  apply Finset.sum_congr rfl
  intro k hk
  have h := (p k).map_smul_univ (fun _ => z) (fun _ => (1 : ℂ))
  simpa [smul_eq_mul, mul_comm] using h.symm

/-- A polynomial zero-free on the closed unit disk remains zero-free on a
strictly larger closed disk. -/
theorem polynomial_exists_zeroFree_larger_disk (h : Polynomial ℂ)
    (hh : ∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0) :
    ∃ R : ℝ, 1 < R ∧ ∀ z : ℂ, ‖z‖ ≤ R → h.eval z ≠ 0 := by
  have hopen : IsOpen {z : ℂ | h.eval z ≠ 0} :=
    isOpen_ne.preimage h.differentiable.continuous
  have hsubset : closedBall (0 : ℂ) 1 ⊆ {z : ℂ | h.eval z ≠ 0} := by
    intro z hz
    exact hh z (by simpa using hz)
  obtain ⟨δ, hδ, hthick⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).exists_cthickening_subset_open hopen hsubset
  rw [cthickening_closedBall hδ.le (by norm_num : (0 : ℝ) ≤ 1)] at hthick
  refine ⟨δ + 1, by linarith, ?_⟩
  intro z hz
  exact hthick (by simpa using hz)

/-- Holomorphicity on a larger closed disk supplies genuine polynomial
approximants uniformly on the closed unit disk. -/
theorem exists_polynomial_tendstoUniformlyOn_of_differentiableOn
    {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) :
    ∃ p : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun N z => (p N).eval z) f atTop
        {z : ℂ | ‖z‖ ≤ 1} := by
  let R₀ : ℝ≥0 := ⟨R, by linarith⟩
  let r : ℝ≥0 := ⟨(1 + R) / 2, by linarith⟩
  have hr : (r : ℝ≥0∞) < (R₀ : ℝ≥0∞) := by
    exact_mod_cast (show (r : ℝ) < (R₀ : ℝ) by change (1 + R) / 2 < R; linarith)
  have hseries : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R₀) 0 R₀ :=
    hf.hasFPowerSeriesOnBall (show 0 < R₀ by exact_mod_cast (show 0 < R by linarith))
  refine ⟨scalarSeriesPolynomial (cauchyPowerSeries f 0 R₀), ?_⟩
  have hconv := hseries.tendstoUniformlyOn hr
  have hsub : {z : ℂ | ‖z‖ ≤ 1} ⊆ ball (0 : ℂ) r := by
    intro z hz
    change ‖z‖ ≤ 1 at hz
    simp only [mem_ball, dist_zero_right]
    change ‖z‖ < (1 + R) / 2
    linarith [hz]
  simpa only [scalarSeriesPolynomial_eval, zero_add] using hconv.mono hsub

/-- The reciprocal of a polynomial zero-free on the closed unit disk is
uniformly approximable there by actual complex polynomials. -/
theorem exists_polynomial_tendstoUniformlyOn_reciprocal (h : Polynomial ℂ)
    (hh : ∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0) :
    ∃ p : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun N z => (p N).eval z) (fun z => (h.eval z)⁻¹)
        atTop {z : ℂ | ‖z‖ ≤ 1} := by
  obtain ⟨R, hR, hzero⟩ := polynomial_exists_zeroFree_larger_disk h hh
  apply exists_polynomial_tendstoUniformlyOn_of_differentiableOn hR
  intro z hz
  exact (h.differentiableAt.inv (hzero z (by simpa using hz))).differentiableWithinAt

end ProofProject
