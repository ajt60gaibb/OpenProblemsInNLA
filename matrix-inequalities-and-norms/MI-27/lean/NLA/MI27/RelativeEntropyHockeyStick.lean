/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nr04_mf14_final_referee_a.

Original MI27 question: Audenaert and Kittaneh. Analytic resolution: Sidney
Holden, Flatiron Institute, Simons Foundation. The identity-shift and pencil
representation follow Peter E. Frenkel; the hockey-stick reformulation
follows Christoph Hirche and Marco Tomamichel. The imported MI24/MI22
spectral/overlap proofs and root-authored inertia proof retain their credits.

The one new helper and unchanged frozen C11 contract were recorded in
HOCKEY-STICK-SUBSTITUTION-STATEMENTS.md before bodies. Root and independent
referee B approved its eight helper headers; the original contract remains
at its original statement gate. This source author runs no Lean or Comparator.
Acceptance requires actual successful compilation and separate final review.
-/
import NLA.MI27.HockeyStickChangeVariables
import NLA.MI27.HockeyStickSubstitution
import NLA.MI27.FiniteHockeyStick

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open MeasureTheory Set
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

lemma c11_relative_entropy_hockey_stick_Ioi {n : ℕ} (hn : 1 ≤ n)
    (X Y : Mat n) (hX : X.PosDef) (hY : Y.PosDef) :
    MeasureTheory.IntegrableOn
      (fun γ : ℝ => E γ X Y / γ + E γ Y X / γ ^ 2) (Set.Ioi (1 : ℝ)) ∧
      relEntropy X Y - trR (X - Y) =
        ∫ γ in Set.Ioi (1 : ℝ), E γ X Y / γ + E γ Y X / γ ^ 2 := by
  let F : ℝ → ℝ := fun t =>
    c11_pencilWeight t * tracePos (-(X + (t : ℂ) • (Y - X)))
  have hbase := c11_relative_entropy_pencil_integral hn X Y hX hY
  have hF : Integrable F := hbase.1
  have hposEq : Set.EqOn
      (fun γ : ℝ => F (γ / (γ - 1)) / (γ - 1) ^ 2)
      (fun γ : ℝ => E γ X Y / γ) (Ioi (1 : ℝ)) := by
    intro γ hγ
    exact c11_pencil_integrand_positive_substitution X Y hX.isHermitian hY.isHermitian γ hγ
  have hnegEq : Set.EqOn
      (fun γ : ℝ => F (-1 / (γ - 1)) / (γ - 1) ^ 2)
      (fun γ : ℝ => E γ Y X / γ ^ 2) (Ioi (1 : ℝ)) := by
    intro γ hγ
    exact c11_pencil_integrand_negative_substitution X Y hX.isHermitian hY.isHermitian γ hγ
  have hposi : IntegrableOn (fun γ : ℝ => E γ X Y / γ) (Ioi (1 : ℝ)) :=
    (integrableOn_congr_fun hposEq measurableSet_Ioi).mp
      ((c11_change_variable_pencil_positive F).1.mp hF.integrableOn)
  have hnegi : IntegrableOn (fun γ : ℝ => E γ Y X / γ ^ 2) (Ioi (1 : ℝ)) :=
    (integrableOn_congr_fun hnegEq measurableSet_Ioi).mp
      ((c11_change_variable_pencil_negative F).1.mp hF.integrableOn)
  have hposInt : (∫ t in Ioi (1 : ℝ), F t) = ∫ γ in Ioi (1 : ℝ), E γ X Y / γ :=
    (c11_change_variable_pencil_positive F).2.trans
      (setIntegral_congr_fun measurableSet_Ioi hposEq)
  have hnegInt : (∫ t in Iio (0 : ℝ), F t) = ∫ γ in Ioi (1 : ℝ), E γ Y X / γ ^ 2 :=
    (c11_change_variable_pencil_negative F).2.trans
      (setIntegral_congr_fun measurableSet_Ioi hnegEq)
  have hrestrict : (∫ t in Iio (0 : ℝ) ∪ Ioi (1 : ℝ), F t) = ∫ t : ℝ, F t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have ht' : 0 ≤ t ∧ t ≤ 1 := by
      simpa only [Set.mem_union, Set.mem_Iio, Set.mem_Ioi, not_or, not_lt] using ht
    change c11_pencilWeight t * tracePos (-(X + (t : ℂ) • (Y - X))) = 0
    rw [c11_pencil_tracePos_zero_unit_interval X Y hX.posSemidef hY.posSemidef t
      ht'.1 ht'.2, mul_zero]
  have hdisj : Disjoint (Iio (0 : ℝ)) (Ioi (1 : ℝ)) := by
    apply Set.disjoint_left.mpr
    intro t ht0 ht1
    have h0 : t < 0 := ht0
    have h1 : 1 < t := ht1
    linarith
  refine ⟨hposi.add hnegi, ?_⟩
  calc
    relEntropy X Y - trR (X - Y) = ∫ t : ℝ, F t := hbase.2
    _ = (∫ t in Iio (0 : ℝ), F t) + ∫ t in Ioi (1 : ℝ), F t := by
      rw [← hrestrict]
      exact setIntegral_union hdisj measurableSet_Ioi hF.integrableOn hF.integrableOn
    _ = (∫ γ in Ioi (1 : ℝ), E γ Y X / γ ^ 2) +
        ∫ γ in Ioi (1 : ℝ), E γ X Y / γ := by rw [hnegInt, hposInt]
    _ = ∫ γ in Ioi (1 : ℝ), E γ X Y / γ + E γ Y X / γ ^ 2 := by
      rw [integral_add hposi hnegi, add_comm]

theorem relative_entropy_finite_hockey_stick {n : ℕ} (hn : 1 ≤ n) (ρ σ : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ) (R : ℝ) (hR : 1 ≤ R)
    (hρσ : ρ ≤ (R : ℂ) • σ) (hσρ : σ ≤ (R : ℂ) • ρ) :
    IntervalIntegrable (fun γ : ℝ => E γ ρ σ / γ + E γ σ ρ / γ ^ 2)
      MeasureTheory.volume 1 R ∧
      relEntropy ρ σ =
        ∫ γ in (1 : ℝ)..R, E γ ρ σ / γ + E γ σ ρ / γ ^ 2 := by
  obtain ⟨hi, he⟩ := c11_relative_entropy_hockey_stick_Ioi hn ρ σ hρ.1 hσ.1
  have htrace : trR (ρ - σ) = 0 := by
    simp only [trR, Matrix.trace_sub, hρ.2, hσ.2, sub_self, Complex.zero_re]
  rw [htrace, sub_zero] at he
  refine ⟨c11_hockey_stick_intervalIntegrable hn ρ σ hρ.1.isHermitian
    hσ.1.isHermitian R hR, ?_⟩
  exact he.trans (c11_integral_Ioi_eq_interval_of_zero_tail
    (fun γ : ℝ => E γ ρ σ / γ + E γ σ ρ / γ ^ 2) R hR hi
      (fun γ hγ => c11_hockey_stick_integrand_zero_tail ρ σ hρ hσ R γ hρσ hσρ hγ))

#print axioms c11_relative_entropy_hockey_stick_Ioi
#assert_trust kernel c11_relative_entropy_hockey_stick_Ioi
#print axioms relative_entropy_finite_hockey_stick
#assert_trust kernel relative_entropy_finite_hockey_stick

end NLA.MI27
