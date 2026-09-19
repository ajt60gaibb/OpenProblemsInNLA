/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nr04_mf14_final_referee_a.

Original MI27 question: Audenaert and Kittaneh. Analytic resolution: Sidney
Holden, Flatiron Institute, Simons Foundation. Relative-entropy pencil:
Peter E. Frenkel. Hockey-stick reformulation: Christoph Hirche and Marco
Tomamichel. Imported MI24/MI22 matrix-CFC source retains its authorship.

All four exact headers were approved by root and independent referee B
before bodies and bound in HOCKEY-STICK-PREBODY-FREEZE.json. These are
matrix linear-combination and positive-part scaling identities, with no
matrix commutation assumption. The source author runs no Lean or Comparator.
-/
import NLA.MI27.PencilIntegral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open MeasureTheory
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

lemma c11_tracePos_smul_nonneg {n : ℕ} (M : Mat n) (hM : M.IsHermitian)
    (a : ℝ) (ha : 0 ≤ a) :
    tracePos ((a : ℂ) • M) = a * tracePos M := by
  have hc := cfc_comp_const_mul a (fun x : ℝ => max x 0) M
    ((M.finite_real_spectrum.image (fun x : ℝ => a * x)).continuousOn _) hM.isSelfAdjoint
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) a M] at hc
  have hfun : (fun x : ℝ => max (a * x) 0) = fun x : ℝ => a * max x 0 := by
    funext x
    simpa only [mul_zero] using (mul_max_of_nonneg x 0 ha).symm
  have hpos : posM ((a : ℂ) • M) = a • posM M := by
    unfold posM
    calc
      cfc (fun x : ℝ => max x 0) ((a : ℂ) • M) =
          cfc (fun x : ℝ => max (a * x) 0) M := by
        convert! hc.symm using 1 <;> rfl
      _ = cfc (fun x : ℝ => a * max x 0) M := by rw [hfun]
      _ = a • cfc (fun x : ℝ => max x 0) M := by
        convert! cfc_const_mul a (fun x : ℝ => max x 0) M
          (M.finite_real_spectrum.continuousOn _) using 1 <;> rfl
  unfold tracePos
  rw [hpos]
  simp only [trR, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

lemma c11_pencil_tracePos_zero_unit_interval {n : ℕ} (X Y : Mat n)
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    tracePos (-(X + (t : ℂ) • (Y - X))) = 0 := by
  have he : X + (t : ℂ) • (Y - X) = ((1 - t : ℝ) : ℂ) • X + (t : ℂ) • Y := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, smul_sub]
    abel
  have hp : (X + (t : ℂ) • (Y - X)).PosSemidef := by
    rw [he]
    exact (hX.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr ht1))).add
      (hY.smul (Complex.zero_le_real.mpr ht0))
  apply le_antisymm ?_ (tracePos_nonneg _)
  have hb := tracePos_le_trR_of_le (-(X + (t : ℂ) • (Y - X))) (0 : Mat n)
    hp.isHermitian.neg Matrix.PosSemidef.zero (neg_nonpos.mpr hp.nonneg)
  simpa only [trR, Matrix.trace_zero, Complex.zero_re] using hb

lemma c11_pencil_integrand_positive_substitution {n : ℕ} (X Y : Mat n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (γ : ℝ) (hγ : 1 < γ) :
    (c11_pencilWeight (γ / (γ - 1)) *
      tracePos (-(X + ((γ / (γ - 1) : ℝ) : ℂ) • (Y - X)))) / (γ - 1) ^ 2 =
        E γ X Y / γ := by
  have hd : 0 < γ - 1 := sub_pos.mpr hγ
  have hg : 0 < γ := lt_trans zero_lt_one hγ
  have hdC : (γ : ℂ) - 1 ≠ 0 := by exact_mod_cast hd.ne'
  have hlin : -(X + ((γ / (γ - 1) : ℝ) : ℂ) • (Y - X)) =
      ((1 / (γ - 1) : ℝ) : ℂ) • (X - (γ : ℂ) • Y) := by
    ext i j
    simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one]
    field_simp [hdC]
    <;> ring
  have hdiff : (X - (γ : ℂ) • Y).IsHermitian :=
    hX.sub (hY.smul (by simp [IsSelfAdjoint]))
  rw [hlin, c11_tracePos_smul_nonneg _ hdiff _ (one_div_nonneg.mpr hd.le)]
  change (c11_pencilWeight (γ / (γ - 1)) * (1 / (γ - 1) * E γ X Y)) /
    (γ - 1) ^ 2 = E γ X Y / γ
  have hsub : γ / (γ - 1) - 1 = 1 / (γ - 1) := by
    field_simp [hd.ne']
    <;> ring
  unfold c11_pencilWeight
  rw [abs_of_pos (div_pos hg hd), hsub]
  field_simp [hd.ne', hg.ne']
  <;> ring

lemma c11_pencil_integrand_negative_substitution {n : ℕ} (X Y : Mat n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (γ : ℝ) (hγ : 1 < γ) :
    (c11_pencilWeight (-1 / (γ - 1)) *
      tracePos (-(X + ((-1 / (γ - 1) : ℝ) : ℂ) • (Y - X)))) / (γ - 1) ^ 2 =
        E γ Y X / γ ^ 2 := by
  have hd : 0 < γ - 1 := sub_pos.mpr hγ
  have hg : 0 < γ := lt_trans zero_lt_one hγ
  have hdC : (γ : ℂ) - 1 ≠ 0 := by exact_mod_cast hd.ne'
  have hlin : -(X + ((-1 / (γ - 1) : ℝ) : ℂ) • (Y - X)) =
      ((1 / (γ - 1) : ℝ) : ℂ) • (Y - (γ : ℂ) • X) := by
    ext i j
    simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_neg]
    field_simp [hdC]
    <;> ring
  have hdiff : (Y - (γ : ℂ) • X).IsHermitian :=
    hY.sub (hX.smul (by simp [IsSelfAdjoint]))
  rw [hlin, c11_tracePos_smul_nonneg _ hdiff _ (one_div_nonneg.mpr hd.le)]
  change (c11_pencilWeight (-1 / (γ - 1)) * (1 / (γ - 1) * E γ Y X)) /
    (γ - 1) ^ 2 = E γ Y X / γ ^ 2
  have hsub : -1 / (γ - 1) - 1 = -γ / (γ - 1) := by
    field_simp [hd.ne']
    <;> ring
  have hneg : -1 / (γ - 1) < 0 := div_neg_of_neg_of_pos (by norm_num) hd
  unfold c11_pencilWeight
  rw [abs_of_neg hneg, hsub]
  field_simp [hd.ne', hg.ne']
  <;> ring

#print axioms c11_tracePos_smul_nonneg
#assert_trust kernel c11_tracePos_smul_nonneg
#print axioms c11_pencil_tracePos_zero_unit_interval
#assert_trust kernel c11_pencil_tracePos_zero_unit_interval
#print axioms c11_pencil_integrand_positive_substitution
#assert_trust kernel c11_pencil_integrand_positive_substitution
#print axioms c11_pencil_integrand_negative_substitution
#assert_trust kernel c11_pencil_integrand_negative_substitution

end NLA.MI27
