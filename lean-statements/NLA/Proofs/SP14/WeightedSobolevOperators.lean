import NLA.Proofs.SP14.WeightedSobolevPhysical

/-!
The literal coefficient-preserving inclusion, truncations, and finite-band
lifts for the weighted sequence spaces. This file supplies the concrete
geometry required by `sobolevOversampling`; background inverse estimates are
not supplied here.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

private noncomputable def boundedDiagonal
    (c : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ n, ‖c n‖ ≤ C) :
    SobolevCoeff 0 →L[ℂ] SobolevCoeff 0 := by
  let f : SobolevCoeff 0 →ₗ[ℂ] SobolevCoeff 0 := {
    toFun := fun x => by
      refine ⟨(fun n => c n * x n), ?_⟩
      have hg : Memℓp (fun n => (C : ℂ) * x n) 2 :=
        (lp.memℓp x).const_smul (C : ℂ)
      apply hg.mono'
      intro n
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hC] using
        (mul_le_mul_of_nonneg_right (hc n) (norm_nonneg (x n)))
    map_add' := by
      intro x y
      apply lp.ext
      funext n
      change c n * (x n + y n) = c n * x n + c n * y n
      ring
    map_smul' := by
      intro a x
      apply lp.ext
      funext n
      simp [mul_left_comm]
  }
  refine f.mkContinuous C ?_
  intro x
  have hpoint (n : ℕ) : ‖f x n‖ ≤ ‖((C : ℂ) • x) n‖ := by
    change ‖c n * x n‖ ≤ ‖(C : ℂ) * x n‖
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hC] using
      (mul_le_mul_of_nonneg_right (hc n) (norm_nonneg (x n)))
  calc
    ‖f x‖ ≤ ‖(C : ℂ) • x‖ := lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) hpoint
    _ = C * ‖x‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]

private theorem boundedDiagonal_apply (c : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ n, ‖c n‖ ≤ C) (x : SobolevCoeff 0) (n : ℕ) :
    boundedDiagonal c C hC hc x n = c n * x n := by
  rfl

private theorem boundedDiagonal_norm_le (c : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ n, ‖c n‖ ≤ C) : ‖boundedDiagonal c C hC hc‖ ≤ C := by
  apply (boundedDiagonal c C hC hc).opNorm_le_bound hC
  intro x
  have hpoint (n : ℕ) : ‖boundedDiagonal c C hC hc x n‖ ≤ ‖((C : ℂ) • x) n‖ := by
    rw [boundedDiagonal_apply]
    change ‖c n * x n‖ ≤ ‖(C : ℂ) * x n‖
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hC] using
      (mul_le_mul_of_nonneg_right (hc n) (norm_nonneg (x n)))
  calc
    ‖boundedDiagonal c C hC hc x‖ ≤ ‖(C : ℂ) • x‖ :=
      lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) hpoint
    _ = C * ‖x‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]

/-- Coefficient-preserving inclusion `H^(s+τ) → H^s` in weighted ℓ² coordinates. -/
noncomputable def sobolevInclusion (s τ : ℝ) (hτ : 0 < τ) :
    SobolevCoeff (s + τ) →L[ℂ] SobolevCoeff s :=
  boundedDiagonal
    (fun n => Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ (-τ))) 1 (by norm_num)
    (by
      intro n
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · norm_cast
        omega
      · linarith)

/-- Literal truncation of coefficients of degree at least `h`. -/
noncomputable def sobolevTruncation (s : ℝ) (h : ℕ) :
    SobolevCoeff s →L[ℂ] SobolevCoeff s :=
  boundedDiagonal (fun n => if n < h then 1 else 0) 1 (by norm_num)
    (by intro n; split_ifs <;> norm_num)

/-- Lift the first `h` physical coefficients from `H^s` to `H^(s+τ)`. -/
noncomputable def sobolevFiniteLift (s τ : ℝ) (h : ℕ) (hτ : 0 < τ) :
    SobolevCoeff s →L[ℂ] SobolevCoeff (s + τ) :=
  boundedDiagonal
    (fun n => if n < h then Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ τ) else 0)
    ((h : ℝ) ^ τ) (Real.rpow_nonneg (by positivity) _)
    (by
      intro n
      by_cases hn : n < h
      · simp only [if_pos hn, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
        apply Real.rpow_le_rpow (by positivity)
        · exact_mod_cast Nat.succ_le_iff.mpr hn
        · exact hτ.le
      · simp only [if_neg hn, norm_zero]
        exact Real.rpow_nonneg (by positivity) _)

theorem sobolevInclusion_apply (s τ : ℝ) (hτ : 0 < τ)
    (x : SobolevCoeff (s + τ)) (n : ℕ) :
    sobolevInclusion s τ hτ x n =
      Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ (-τ)) * x n := by
  unfold sobolevInclusion
  rw [boundedDiagonal_apply]

theorem sobolevTruncation_apply (s : ℝ) (h : ℕ)
    (x : SobolevCoeff s) (n : ℕ) :
    sobolevTruncation s h x n = if n < h then x n else 0 := by
  unfold sobolevTruncation
  rw [boundedDiagonal_apply]
  split_ifs <;> simp

theorem sobolevFiniteLift_apply (s τ : ℝ) (h : ℕ) (hτ : 0 < τ)
    (x : SobolevCoeff s) (n : ℕ) :
    sobolevFiniteLift s τ h hτ x n =
      if n < h then Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ τ) * x n else 0 := by
  unfold sobolevFiniteLift
  rw [boundedDiagonal_apply]
  split_ifs <;> simp

theorem sobolevInclusion_norm_le (s τ : ℝ) (hτ : 0 < τ) :
    ‖sobolevInclusion s τ hτ‖ ≤ 1 := by
  unfold sobolevInclusion
  exact boundedDiagonal_norm_le _ _ _ _

theorem sobolevTruncation_norm_le (s : ℝ) (h : ℕ) :
    ‖sobolevTruncation s h‖ ≤ 1 := by
  unfold sobolevTruncation
  exact boundedDiagonal_norm_le _ _ _ _

theorem sobolevFiniteLift_norm_le (s τ : ℝ) (h : ℕ) (hτ : 0 < τ) :
    ‖sobolevFiniteLift s τ h hτ‖ ≤ (h : ℝ) ^ τ := by
  unfold sobolevFiniteLift
  exact boundedDiagonal_norm_le _ _ _ _

theorem physicalCoeff_inclusion (s τ : ℝ) (hτ : 0 < τ)
    (x : SobolevCoeff (s + τ)) (n : ℕ) :
    physicalCoeff s (sobolevInclusion s τ hτ x) n =
      physicalCoeff (s + τ) x n := by
  have hn : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hp : ((n + 1 : ℕ) : ℝ) ^ (-s) * ((n + 1 : ℕ) : ℝ) ^ (-τ) =
      ((n + 1 : ℕ) : ℝ) ^ (-(s + τ)) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  simp only [physicalCoeff, sobolevInclusion_apply, ← mul_assoc,
    ← Complex.ofReal_mul, hp]

theorem physicalCoeff_truncation (s : ℝ) (h : ℕ)
    (x : SobolevCoeff s) (n : ℕ) :
    physicalCoeff s (sobolevTruncation s h x) n =
      if n < h then physicalCoeff s x n else 0 := by
  by_cases hn : n < h
  · simp [physicalCoeff, sobolevTruncation_apply, hn]
  · simp [physicalCoeff, sobolevTruncation_apply, hn]

theorem physicalCoeff_finiteLift (s τ : ℝ) (h : ℕ) (hτ : 0 < τ)
    (x : SobolevCoeff s) (n : ℕ) :
    physicalCoeff (s + τ) (sobolevFiniteLift s τ h hτ x) n =
      if n < h then physicalCoeff s x n else 0 := by
  by_cases hn : n < h
  · have hn' : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
    have hp : ((n + 1 : ℕ) : ℝ) ^ (-(s + τ)) * ((n + 1 : ℕ) : ℝ) ^ τ =
        ((n + 1 : ℕ) : ℝ) ^ (-s) := by
      rw [← Real.rpow_add hn']
      congr 1
      ring
    simp only [physicalCoeff, sobolevFiniteLift_apply, if_pos hn,
      ← mul_assoc, ← Complex.ofReal_mul, hp]
  · simp [physicalCoeff, sobolevFiniteLift_apply, hn]

theorem sobolevTruncation_idempotent (s : ℝ) (h : ℕ) :
    sobolevTruncation s h * sobolevTruncation s h = sobolevTruncation s h := by
  ext x n
  by_cases hn : n < h
  · simp [mul_apply_eq_comp, sobolevTruncation_apply, hn]
  · simp [mul_apply_eq_comp, sobolevTruncation_apply, hn]

theorem sobolevTruncation_zero (s : ℝ) : sobolevTruncation s 0 = 0 := by
  ext x n
  simp [sobolevTruncation_apply]

theorem sobolevFiniteLift_zero (s τ : ℝ) (hτ : 0 < τ) :
    sobolevFiniteLift s τ 0 hτ = 0 := by
  ext x n
  simp [sobolevFiniteLift_apply]

theorem sobolevInclusion_comp_finiteLift (s τ : ℝ) (h : ℕ) (hτ : 0 < τ) :
    (sobolevInclusion s τ hτ).comp (sobolevFiniteLift s τ h hτ) =
      sobolevTruncation s h := by
  ext x n
  by_cases hn : n < h
  · have hn' : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
    have hp : ((n + 1 : ℕ) : ℝ) ^ (-τ) * ((n + 1 : ℕ) : ℝ) ^ τ = 1 := by
      rw [← Real.rpow_add hn']
      simp
    simp only [ContinuousLinearMap.comp_apply, sobolevInclusion_apply,
      sobolevFiniteLift_apply, sobolevTruncation_apply, if_pos hn,
      ← mul_assoc, ← Complex.ofReal_mul, hp, Complex.ofReal_one, one_mul]
  · simp [ContinuousLinearMap.comp_apply, sobolevInclusion_apply,
      sobolevFiniteLift_apply, sobolevTruncation_apply, hn]

/-- The source's sharp tail estimate, including `q=0`. -/
theorem sobolev_tail_estimate (s τ : ℝ) (hτ : 0 < τ) (q : ℕ)
    (x : SobolevCoeff (s + τ)) :
    ‖((1 - sobolevTruncation s q).comp (sobolevInclusion s τ hτ)) x‖ ≤
      (((q + 1 : ℕ) : ℝ) ^ (-τ)) * ‖x‖ := by
  let C : ℝ := (((q + 1 : ℕ) : ℝ) ^ (-τ))
  have hC : 0 ≤ C := Real.rpow_nonneg (by positivity) _
  have hpoint (n : ℕ) :
      ‖(((1 - sobolevTruncation s q).comp (sobolevInclusion s τ hτ)) x) n‖ ≤
        ‖((C : ℂ) • x) n‖ := by
    have hcoord : (((1 - sobolevTruncation s q).comp (sobolevInclusion s τ hτ)) x) n =
        if n < q then 0 else
          Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ (-τ)) * x n := by
      by_cases hn : n < q
      · simp [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self,
          sobolevTruncation_apply, sobolevInclusion_apply, hn]
      · simp [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self,
          sobolevTruncation_apply, sobolevInclusion_apply, hn]
    rw [hcoord]
    by_cases hn : n < q
    · simp [hn]
    · simp only [if_neg hn]
      have hbase : (((q + 1 : ℕ) : ℝ)) ≤ (((n + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.succ_le_succ (Nat.le_of_not_gt hn)
      have hpow : ((n + 1 : ℕ) : ℝ) ^ (-τ) ≤ C :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
      change ‖Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ (-τ)) * x n‖ ≤
        ‖(C : ℂ) * x n‖
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by positivity) _), abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right hpow (norm_nonneg (x n))
  calc
    ‖((1 - sobolevTruncation s q).comp (sobolevInclusion s τ hτ) x)‖ ≤
        ‖(C : ℂ) • x‖ := lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) hpoint
    _ = C * ‖x‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hC]

private theorem finiteLift_comp_truncation (s τ : ℝ) (h : ℕ) (hτ : 0 < τ) :
    (sobolevFiniteLift s τ h hτ).comp (sobolevTruncation s h) =
      sobolevFiniteLift s τ h hτ := by
  ext x n
  by_cases hn : n < h
  · simp [ContinuousLinearMap.comp_apply, sobolevFiniteLift_apply,
      sobolevTruncation_apply, hn]
  · simp [ContinuousLinearMap.comp_apply, sobolevFiniteLift_apply, hn]

/-- The source's sharp finite-band estimate, including `h=0`. -/
theorem sobolev_finiteBand_estimate (s τ : ℝ) (h : ℕ) (hτ : 0 < τ)
    (y : SobolevCoeff s) :
    ‖sobolevFiniteLift s τ h hτ y‖ ≤
      ((h : ℝ) ^ τ) * ‖sobolevTruncation s h y‖ := by
  have hLPh := congrArg (fun f : SobolevCoeff s →L[ℂ] SobolevCoeff (s + τ) => f y)
    (finiteLift_comp_truncation s τ h hτ)
  calc
    ‖sobolevFiniteLift s τ h hτ y‖ =
        ‖sobolevFiniteLift s τ h hτ (sobolevTruncation s h y)‖ := by
          simpa only [ContinuousLinearMap.comp_apply] using congrArg norm hLPh.symm
    _ ≤ ‖sobolevFiniteLift s τ h hτ‖ * ‖sobolevTruncation s h y‖ :=
      (sobolevFiniteLift s τ h hτ).le_opNorm _
    _ ≤ ((h : ℝ) ^ τ) * ‖sobolevTruncation s h y‖ :=
      mul_le_mul_of_nonneg_right (sobolevFiniteLift_norm_le s τ h hτ) (norm_nonneg _)

end NLA.Proofs.SP14
