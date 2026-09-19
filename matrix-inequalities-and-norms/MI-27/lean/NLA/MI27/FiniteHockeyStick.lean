/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/recover_published_coverage.

Original MI27 resolution: Sidney Holden, Center for Computational Biology,
Flatiron Institute, Simons Foundation. Relative-entropy input: Péter E. Frenkel,
Christoph Hirche and Marco Tomamichel. Existing MI24/MI27 credits are retained.

UNCOMPILED partial C11 helpers, requiring root compilation and independent review.
This file does NOT prove the general noncommuting entropy/integral identity.
It proves finite integrability, exact zero tails, the R=1 case, and independence
of a larger finite cutoff. No identity is assumed as a new axiom or premise.
-/
import NLA.MI27.UniformCutoff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

/-- F1: both ordinary scalar denominators are nonzero on the complete closed interval. -/
lemma c11_hockey_stick_integrand_continuousOn {n : ℕ} (hn : 1 ≤ n)
    (X Y : Mat n) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (R : ℝ) (hR : 1 ≤ R) :
    ContinuousOn (fun γ : ℝ => E γ X Y / γ + E γ Y X / γ ^ 2) (Set.Icc 1 R) := by
  have hx : ContinuousOn (fun γ : ℝ => E γ X Y) (Set.Icc 1 R) :=
    (hockey_stick_continuous_gamma hn X Y hX hY).continuousOn
  have hy : ContinuousOn (fun γ : ℝ => E γ Y X) (Set.Icc 1 R) :=
    (hockey_stick_continuous_gamma hn Y X hY hX).continuousOn
  have hne : ∀ γ ∈ Set.Icc (1 : ℝ) R, γ ≠ 0 := by
    intro γ hγ
    exact (lt_of_lt_of_le zero_lt_one hγ.1).ne'
  exact (hx.div continuousOn_id hne).add
    (hy.div (continuousOn_id.pow 2) (fun γ hγ => pow_ne_zero 2 (hne γ hγ)))

lemma c11_hockey_stick_intervalIntegrable {n : ℕ} (hn : 1 ≤ n)
    (X Y : Mat n) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (R : ℝ) (hR : 1 ≤ R) :
    IntervalIntegrable (fun γ : ℝ => E γ X Y / γ + E γ Y X / γ ^ 2)
      MeasureTheory.volume 1 R :=
  (c11_hockey_stick_integrand_continuousOn hn X Y hX hY R hR).intervalIntegrable_of_Icc hR

/-- The actual spectral positive part vanishes when its Hermitian argument is nonpositive. -/
lemma c11_hockey_stick_zero_of_le {n : ℕ} (X Y : Mat n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (γ : ℝ)
    (hXY : X ≤ (γ : ℂ) • Y) : E γ X Y = 0 := by
  apply le_antisymm ?_ (tracePos_nonneg _)
  have hγY : ((γ : ℂ) • Y).IsHermitian :=
    hY.smul (by simp [IsSelfAdjoint])
  have hh := tracePos_le_trR_of_le (X - (γ : ℂ) • Y) (0 : Mat n)
    (hX.sub hγY) Matrix.PosSemidef.zero (sub_nonpos.mpr hXY)
  simpa only [E, trR, Matrix.trace_zero, Complex.zero_re] using hh

/-- F2: an original supplied Loewner cutoff removes the whole tail, including its endpoint. -/
lemma c11_hockey_stick_zero_tail {n : ℕ} (X Y : Mat n)
    (hX : X.IsHermitian) (hY : Y.PosSemidef) (R γ : ℝ)
    (hXY : X ≤ (R : ℂ) • Y) (hRγ : R ≤ γ) : E γ X Y = 0 := by
  have hRγC : (R : ℂ) ≤ (γ : ℂ) := by exact_mod_cast hRγ
  exact c11_hockey_stick_zero_of_le X Y hX hY.isHermitian γ
    (hXY.trans (smul_le_smul_of_nonneg_right hRγC hY.nonneg))

lemma c11_hockey_stick_integrand_zero_tail {n : ℕ} (ρ σ : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ) (R γ : ℝ)
    (hρσ : ρ ≤ (R : ℂ) • σ) (hσρ : σ ≤ (R : ℂ) • ρ)
    (hRγ : R ≤ γ) : E γ ρ σ / γ + E γ σ ρ / γ ^ 2 = 0 := by
  rw [c11_hockey_stick_zero_tail ρ σ hρ.1.isHermitian hσ.1.posSemidef R γ hρσ hRγ,
    c11_hockey_stick_zero_tail σ ρ hσ.1.isHermitian hρ.1.posSemidef R γ hσρ hRγ]
  simp only [zero_div, add_zero]

/-- F3: the original degenerate cutoff forces equality of the inputs. -/
lemma c11_relative_entropy_cutoff_one {n : ℕ} (hn : 1 ≤ n) (ρ σ : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ)
    (hρσ : ρ ≤ ((1 : ℝ) : ℂ) • σ) (hσρ : σ ≤ ((1 : ℝ) : ℂ) • ρ) :
    IntervalIntegrable (fun γ : ℝ => E γ ρ σ / γ + E γ σ ρ / γ ^ 2)
      MeasureTheory.volume 1 1 ∧
      relEntropy ρ σ =
        ∫ γ in (1 : ℝ)..1, E γ ρ σ / γ + E γ σ ρ / γ ^ 2 := by
  have heq : ρ = σ := le_antisymm (by simpa only [Complex.ofReal_one, one_smul] using hρσ)
    (by simpa only [Complex.ofReal_one, one_smul] using hσρ)
  refine ⟨c11_hockey_stick_intervalIntegrable hn ρ σ hρ.1.isHermitian
    hσ.1.isHermitian 1 le_rfl, ?_⟩
  rw [heq]
  simp only [relEntropy, sub_self, mul_zero, trR, Matrix.trace_zero,
    Complex.zero_re, intervalIntegral.integral_same]

/-- F4: enlarging a valid two-sided cutoff does not change the literal finite integral. -/
lemma c11_hockey_stick_integral_cutoff_independent {n : ℕ} (hn : 1 ≤ n) (ρ σ : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ) (R S : ℝ)
    (hR : 1 ≤ R) (hRS : R ≤ S)
    (hρσ : ρ ≤ (R : ℂ) • σ) (hσρ : σ ≤ (R : ℂ) • ρ) :
    (∫ γ in (1 : ℝ)..S, E γ ρ σ / γ + E γ σ ρ / γ ^ 2) =
      ∫ γ in (1 : ℝ)..R, E γ ρ σ / γ + E γ σ ρ / γ ^ 2 := by
  let f : ℝ → ℝ := fun γ => E γ ρ σ / γ + E γ σ ρ / γ ^ 2
  have h1R : IntervalIntegrable f MeasureTheory.volume 1 R :=
    c11_hockey_stick_intervalIntegrable hn ρ σ hρ.1.isHermitian hσ.1.isHermitian R hR
  have hRSint : IntervalIntegrable f MeasureTheory.volume R S := by
    have hc := (c11_hockey_stick_integrand_continuousOn hn ρ σ hρ.1.isHermitian
      hσ.1.isHermitian S (hR.trans hRS)).mono
      (show Set.Icc R S ⊆ Set.Icc 1 S from fun _ hγ => ⟨hR.trans hγ.1, hγ.2⟩)
    exact hc.intervalIntegrable_of_Icc hRS
  have hzero : (∫ γ in R..S, f γ) = 0 := by
    calc
      (∫ γ in R..S, f γ) = ∫ _γ in R..S, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro γ hγ
        exact c11_hockey_stick_integrand_zero_tail ρ σ hρ hσ R γ hρσ hσρ
          ((Set.uIcc_of_le hRS ▸ hγ).1)
      _ = 0 := by simp only [intervalIntegral.integral_zero]
  have hadd := intervalIntegral.integral_add_adjacent_intervals h1R hRSint
  simpa only [hzero, add_zero, f] using hadd.symm

#print axioms c11_hockey_stick_integral_cutoff_independent
#print axioms c11_relative_entropy_cutoff_one

end NLA.MI27
