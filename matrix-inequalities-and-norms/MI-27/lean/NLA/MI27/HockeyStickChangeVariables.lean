/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nr04_mf14_final_referee_a.

Original MI27 question: Audenaert and Kittaneh. Analytic resolution: Sidney
Holden, Flatiron Institute, Simons Foundation. The relative-entropy pencil
identity is due to Peter E. Frenkel; its hockey-stick reformulation follows
Christoph Hirche and Marco Tomamichel. This file uses pinned Mathlib's
one-dimensional Jacobian theorem, retaining its source authorship.

Exact headers were approved by root and independent referee B before any
bodies; see HOCKEY-STICK-PREBODY-FREEZE.json. Both changes of variables
include their actual integrability equivalence. The source author runs no
Lean or Comparator. Full C11 is not asserted in this scalar module.
-/
import NLA.MI27.Definitions
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open MeasureTheory Set
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

lemma c11_change_variable_pencil_positive (f : ℝ → ℝ) :
    (MeasureTheory.IntegrableOn f (Set.Ioi (1 : ℝ)) ↔
      MeasureTheory.IntegrableOn
        (fun γ : ℝ => f (γ / (γ - 1)) / (γ - 1) ^ 2) (Set.Ioi (1 : ℝ))) ∧
      (∫ t in Set.Ioi (1 : ℝ), f t) =
        ∫ γ in Set.Ioi (1 : ℝ), f (γ / (γ - 1)) / (γ - 1) ^ 2 := by
  let u : ℝ → ℝ := fun x => x / (x - 1)
  have hmap (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) : u x ∈ Ioi (1 : ℝ) := by
    change 1 < x / (x - 1)
    exact (lt_div_iff₀ (sub_pos.mpr hx)).2 (by linarith)
  have hinv (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) : u (u x) = x := by
    have hx0 : x - 1 ≠ 0 := (sub_pos.mpr hx).ne'
    have he : u x - 1 = 1 / (x - 1) := by
      dsimp [u]
      field_simp [hx0]
      <;> ring
    change u x / (u x - 1) = x
    rw [he]
    dsimp [u]
    field_simp [hx0]
  have hinj : Set.InjOn u (Ioi (1 : ℝ)) := by
    intro x hx y hy hxy
    have he := congrArg u hxy
    simpa only [hinv x hx, hinv y hy] using he
  have himage : u '' Ioi (1 : ℝ) = Ioi (1 : ℝ) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hmap x hx
    · intro hy
      exact ⟨u y, hmap y hy, hinv y hy⟩
  have hd : ∀ x ∈ Ioi (1 : ℝ),
      HasDerivWithinAt u (-1 / (x - 1) ^ 2) (Ioi (1 : ℝ)) x := by
    intro x hx
    have hd₀ := (hasDerivAt_id x).div ((hasDerivAt_id x).sub_const 1)
      (sub_pos.mpr hx).ne'
    have he : (1 * (x - 1) - x * 1) / (x - 1) ^ 2 = -1 / (x - 1) ^ 2 := by ring
    have hd₁ : HasDerivAt u (-1 / (x - 1) ^ 2) x := by
      convert! hd₀.congr_deriv he using 1 <;> rfl
    exact hd₁.hasDerivWithinAt
  have hjac : Set.EqOn
      (fun x : ℝ => |-1 / (x - 1) ^ 2| • f (u x))
      (fun x : ℝ => f (u x) / (x - 1) ^ 2) (Ioi (1 : ℝ)) := by
    intro x _
    change |-1 / (x - 1) ^ 2| • f (u x) = f (u x) / (x - 1) ^ 2
    rw [abs_div, abs_of_nonneg (sq_nonneg (x - 1))]
    norm_num only [abs_neg, abs_one, smul_eq_mul]
    ring
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hd hinj f
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj f
  rw [himage] at hi he
  refine ⟨hi.trans (integrableOn_congr_fun hjac measurableSet_Ioi), ?_⟩
  exact he.trans (setIntegral_congr_fun measurableSet_Ioi hjac)

lemma c11_change_variable_pencil_negative (f : ℝ → ℝ) :
    (MeasureTheory.IntegrableOn f (Set.Iio (0 : ℝ)) ↔
      MeasureTheory.IntegrableOn
        (fun γ : ℝ => f (-1 / (γ - 1)) / (γ - 1) ^ 2) (Set.Ioi (1 : ℝ))) ∧
      (∫ t in Set.Iio (0 : ℝ), f t) =
        ∫ γ in Set.Ioi (1 : ℝ), f (-1 / (γ - 1)) / (γ - 1) ^ 2 := by
  let u : ℝ → ℝ := fun x => -1 / (x - 1)
  have hmap (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) : u x ∈ Iio (0 : ℝ) := by
    change -1 / (x - 1) < 0
    exact div_neg_of_neg_of_pos (by norm_num) (sub_pos.mpr (show 1 < x from hx))
  have hleft (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) : 1 - 1 / u x = x := by
    have hx0 : x - 1 ≠ 0 := (show (0 : ℝ) < x - 1 from sub_pos.mpr hx).ne'
    dsimp [u]
    field_simp [hx0]
    <;> ring
  have hinj : Set.InjOn u (Ioi (1 : ℝ)) := by
    intro x hx y hy hxy
    have he := congrArg (fun z : ℝ => 1 - 1 / z) hxy
    simpa only [hleft x hx, hleft y hy] using he
  have himage : u '' Ioi (1 : ℝ) = Iio (0 : ℝ) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hmap x hx
    · intro hy
      have hy0 : y < 0 := hy
      have harg : 1 < 1 - 1 / y := by
        have hdiv : 1 / y < 0 := div_neg_of_pos_of_neg zero_lt_one hy0
        linarith
      refine ⟨1 - 1 / y, harg, ?_⟩
      have he : (1 - 1 / y) - 1 = -1 / y := by ring
      change -1 / ((1 - 1 / y) - 1) = y
      rw [he]
      field_simp [hy0.ne]
  have hd : ∀ x ∈ Ioi (1 : ℝ),
      HasDerivWithinAt u (1 / (x - 1) ^ 2) (Ioi (1 : ℝ)) x := by
    intro x hx
    have hd₀ := (hasDerivAt_const x (-1 : ℝ)).div ((hasDerivAt_id x).sub_const 1)
      (sub_pos.mpr hx).ne'
    have he : (0 * (x - 1) - (-1) * 1) / (x - 1) ^ 2 = 1 / (x - 1) ^ 2 := by ring
    have hd₁ : HasDerivAt u (1 / (x - 1) ^ 2) x := by
      convert! hd₀.congr_deriv he using 1 <;> rfl
    exact hd₁.hasDerivWithinAt
  have hjac : Set.EqOn
      (fun x : ℝ => |1 / (x - 1) ^ 2| • f (u x))
      (fun x : ℝ => f (u x) / (x - 1) ^ 2) (Ioi (1 : ℝ)) := by
    intro x _
    change |1 / (x - 1) ^ 2| • f (u x) = f (u x) / (x - 1) ^ 2
    rw [abs_of_nonneg (one_div_nonneg.mpr (sq_nonneg (x - 1))), smul_eq_mul]
    ring
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hd hinj f
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj f
  rw [himage] at hi he
  refine ⟨hi.trans (integrableOn_congr_fun hjac measurableSet_Ioi), ?_⟩
  exact he.trans (setIntegral_congr_fun measurableSet_Ioi hjac)

lemma c11_integral_Ioi_eq_interval_of_zero_tail (f : ℝ → ℝ) (R : ℝ) (hR : 1 ≤ R)
    (hf : MeasureTheory.IntegrableOn f (Set.Ioi (1 : ℝ)))
    (hzero : ∀ γ : ℝ, R ≤ γ → f γ = 0) :
    (∫ γ in Set.Ioi (1 : ℝ), f γ) = ∫ γ in (1 : ℝ)..R, f γ := by
  have hz : (∫ γ in Set.Ioi R, f γ) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun γ hγ => hzero γ hγ.le)
  simpa only [hz, sub_zero] using intervalIntegral.integral_Ioi_sub_Ioi hf hR

#print axioms c11_change_variable_pencil_positive
#assert_trust kernel c11_change_variable_pencil_positive
#print axioms c11_change_variable_pencil_negative
#assert_trust kernel c11_change_variable_pencil_negative
#print axioms c11_integral_Ioi_eq_interval_of_zero_tail
#assert_trust kernel c11_integral_Ioi_eq_interval_of_zero_tail

end NLA.MI27
