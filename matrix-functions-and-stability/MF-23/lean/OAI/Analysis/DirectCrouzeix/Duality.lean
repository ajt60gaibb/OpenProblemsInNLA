import OAI.Analysis.DirectCrouzeix.SingularPairs

namespace OAI

universe u_41 u_42 u_43 u_44 u_45

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem weighted_coefficient_dual {ρ : Type u_41} {ι : Type u_42} {κ : Type u_43}
    [Fintype ρ] [Fintype ι] [Fintype κ]
    (P : ρ → Matrix ι κ ℂ) (w : ρ → ℝ) (hw : ∀ k, 0 < w k)
    (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ C : ρ → Matrix ι κ ℂ,
      ‖∑ k, entryPair (P k) (C k)‖ ^ 2 ≤ b * ∑ k, w k * hsSq (C k)) :
    (∑ k, hsSq (P k) / w k) ≤ b := by
  let C : ρ → Matrix ι κ ℂ := fun k => ((w k : ℂ)⁻¹) • (P k).map star
  let s : ℝ := ∑ k, hsSq (P k) / w k
  have hs : 0 ≤ s := Finset.sum_nonneg (fun k _ => div_nonneg (hsSq_nonneg _) (hw k).le)
  have hp : (∑ k, entryPair (P k) (C k)) = (s : ℂ) := by
    simp only [C, entryPair_smul_right, entryPair_conj, s, Complex.ofReal_sum,
      Complex.ofReal_div]
    apply Finset.sum_congr rfl
    intro k _
    simp only [div_eq_mul_inv]
    ring
  have he : (∑ k, w k * hsSq (C k)) = s := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [C, hsSq_smul, hsSq_map_star, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hw k)]
    field_simp
  have ht := h C
  rw [hp, he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs] at ht
  by_cases hs0 : s = 0
  · change s ≤ b
    simpa [hs0] using hb
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    change s ≤ b
    apply (mul_le_mul_iff_left₀ hspos).mp
    nlinarith

open MeasureTheory

theorem weighted_integral_norm_sq_le {α : Type u_44} {E : Type u_45} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) (k : α → ℝ) (u : α → E)
    (hk : ∀ x, 0 ≤ k x) (hki : Integrable k μ)
    (hui : Integrable (fun x => k x • u x) μ)
    (hsqi : Integrable (fun x => k x * ‖u x‖ ^ 2) μ)
    (hmass : ∫ x, k x ∂μ = 1) :
    ‖∫ x, k x • u x ∂μ‖ ^ 2 ≤ ∫ x, k x * ‖u x‖ ^ 2 ∂μ := by
  let v := ∫ x, k x • u x ∂μ
  have hii : Integrable (fun x => inner ℝ v (k x • u x)) μ :=
    (innerSL ℝ v).integrable_comp hui
  have hi : (∫ x, inner ℝ v (k x • u x) ∂μ) = ‖v‖ ^ 2 := by
    change (∫ x, (innerSL ℝ v) (k x • u x) ∂μ) = _
    rw [(innerSL ℝ v).integral_comp_comm hui]
    exact real_inner_self_eq_norm_sq v
  have hn : 0 ≤ ∫ x, k x * ‖u x - v‖ ^ 2 ∂μ :=
    integral_nonneg (fun x => mul_nonneg (hk x) (sq_nonneg _))
  have hexp : (fun x => k x * ‖u x - v‖ ^ 2) =
      fun x => (k x * ‖u x‖ ^ 2 - 2 * inner ℝ v (k x • u x)) + k x * ‖v‖ ^ 2 := by
    funext x
    rw [norm_sub_sq_real, inner_smul_right, real_inner_comm v (u x)]
    ring
  rw [hexp] at hn
  have hsubi : Integrable (fun x => k x * ‖u x‖ ^ 2 - 2 * inner ℝ v (k x • u x)) μ :=
    hsqi.sub (hii.const_mul 2)
  have hconsti : Integrable (fun x => k x * ‖v‖ ^ 2) μ := hki.mul_const _
  rw [integral_add hsubi hconsti, integral_sub hsqi (hii.const_mul 2),
    integral_const_mul, integral_mul_const, hi, hmass] at hn
  change ‖v‖ ^ 2 ≤ _
  linarith

end DirectCrouzeix

end

end OAI
