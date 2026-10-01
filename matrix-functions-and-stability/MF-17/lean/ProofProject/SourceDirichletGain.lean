import ProofProject.SourceRadialIntegrability
import ProofProject.SourcePhasePolar
import ProofProject.WeightedDirichletBounds

/-!
# Explicit Dirichlet gain for the actual source weight

The central singularity supplies numerator growth, while the reflected weight
vanishes at the central point. The integrable remainder away from that point
is bounded uniformly in the degree. All weights here are the source's actual
principal-power factor.
-/

noncomputable section

open MeasureTheory

namespace ProofProject

def sourceAngularWeight (α θ : ℝ) : ℝ := ‖sourceWeightFactor α (sourceCircle θ)‖ ^ 2

def sourceReflectedWeight (α θ : ℝ) : ℝ := ‖sourceWeightFactor α (-sourceCircle θ)‖ ^ 2

lemma sourceCircle_add_pi (θ : ℝ) : sourceCircle (θ + Real.pi) = -sourceCircle θ := by
  apply Complex.ext <;> simp [sourceCircle_re, sourceCircle_im]

lemma sourceCircle_periodic : Function.Periodic sourceCircle (2 * Real.pi) := by
  intro θ
  apply Complex.ext <;> simp [sourceCircle_re, sourceCircle_im]

lemma sourceAngularWeight_periodic (α : ℝ) :
    Function.Periodic (sourceAngularWeight α) (2 * Real.pi) := by
  intro θ
  simp only [sourceAngularWeight, sourceCircle_periodic θ]

lemma sourceReflectedWeight_eq_shift (α θ : ℝ) :
    sourceReflectedWeight α θ = sourceAngularWeight α (θ + Real.pi) := by
  simp only [sourceReflectedWeight, sourceAngularWeight, sourceCircle_add_pi]

lemma sourceAngularWeight_intervalIntegrable {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (a b : ℝ) : IntervalIntegrable (sourceAngularWeight α) volume a b := by
  have hi : IntervalIntegrable (sourceAngularWeight α) volume (-Real.pi) Real.pi := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])).mpr
    convert! sourceWeightFactor_radial_norm_sq_integrable hα0 hα1
      (r := 1) (by norm_num) le_rfl using 1 <;>
      simp only [Complex.ofReal_one, one_mul] <;> rfl
  exact (sourceAngularWeight_periodic α).intervalIntegrable (by positivity)
    (by convert hi using 1 <;> ring) a b

lemma sourceReflectedWeight_intervalIntegrable {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (a b : ℝ) : IntervalIntegrable (sourceReflectedWeight α) volume a b := by
  have hi := (sourceAngularWeight_intervalIntegrable hα0 hα1
    (a + Real.pi) (b + Real.pi)).comp_add_right Real.pi
  simpa only [add_sub_cancel_right, ← sourceReflectedWeight_eq_shift] using hi

lemma sourceAngularWeight_kernel_integrable {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun θ => sourceAngularWeight α θ * ‖dirichletKernel n θ‖ ^ 2)
      volume a b :=
  (sourceAngularWeight_intervalIntegrable hα0 hα1 a b).mul_continuousOn
    ((continuous_dirichletKernel n).norm.pow 2).continuousOn

lemma sourceReflectedWeight_kernel_integrable {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun θ => sourceReflectedWeight α θ * ‖dirichletKernel n θ‖ ^ 2)
      volume a b :=
  (sourceReflectedWeight_intervalIntegrable hα0 hα1 a b).mul_continuousOn
    ((continuous_dirichletKernel n).norm.pow 2).continuousOn

/-- On the short central arc the numerator chord is at least one. -/
lemma sourceCircle_add_chord_one_le {θ : ℝ} (hθ : |θ| ≤ 1) :
    1 ≤ ‖1 + sourceCircle θ‖ := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := θ)
  have hs : θ ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg θ) hθ 2
  have hn := Complex.re_le_norm (1 + sourceCircle θ)
  simp only [Complex.add_re, Complex.one_re, sourceCircle_re] at hn
  linarith

lemma sourceCircle_sub_chord_le_abs (θ : ℝ) : ‖1 - sourceCircle θ‖ ≤ |θ| := by
  simpa only [sourceCircle, norm_sub_rev, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ))

/-- The actual weight has the central lower singularity with an explicit coefficient. -/
lemma sourceAngularWeight_lower_central {α θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hθ0 : 0 < |θ|) (hθ1 : |θ| ≤ 1) :
    Real.exp (-2 * sourceWeightCorrectionBound α) * |θ| ^ (-α) ≤
      sourceAngularWeight α θ := by
  have hp := sourceCircle_add_chord_one_le hθ1
  have hm := sourceCircle_sub_chord_le_abs θ
  have hden : 0 < ‖1 - sourceCircle θ‖ := by
    have hchord := source_radial_chord_lower (r := 1) (by norm_num) le_rfl
      (hθ1.trans (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi))
    simp only [Complex.ofReal_one, one_mul] at hchord
    exact (div_pos hθ0 Real.pi_pos).trans_le hchord
  have hratio : |θ| ^ (-α) ≤ ‖1 + sourceCircle θ‖ ^ α / ‖1 - sourceCircle θ‖ ^ α := by
    rw [Real.rpow_neg (abs_nonneg _), ← one_div]
    exact div_le_div₀ (Real.rpow_nonneg (norm_nonneg _) _)
      (by simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hp hα0.le)
      (Real.rpow_pos_of_pos hden _) (Real.rpow_le_rpow hden.le hm hα0.le)
  exact (mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le).trans
    (sourceWeightFactor_norm_sq_bounds hα0 hα1 (by simp : ‖sourceCircle θ‖ ≤ 1)).1

/-- The reflected actual weight vanishes to order α on the central arc. -/
lemma sourceReflectedWeight_upper_central {α θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hθ1 : |θ| ≤ 1) :
    sourceReflectedWeight α θ ≤
      Real.exp (2 * sourceWeightCorrectionBound α) * |θ| ^ α := by
  have hp := sourceCircle_add_chord_one_le hθ1
  have hm := sourceCircle_sub_chord_le_abs θ
  have hu := (sourceWeightFactor_norm_sq_bounds hα0 hα1
    (by simp : ‖-sourceCircle θ‖ ≤ 1)).2
  simp only [← sub_eq_add_neg, sub_neg_eq_add] at hu
  have hratio : ‖1 - sourceCircle θ‖ ^ α / ‖1 + sourceCircle θ‖ ^ α ≤ |θ| ^ α := by
    calc
      _ ≤ |θ| ^ α / (1 : ℝ) := div_le_div₀ (Real.rpow_nonneg (abs_nonneg _) _)
        (Real.rpow_le_rpow (norm_nonneg _) hm hα0.le) (by norm_num)
        (by simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hp hα0.le)
      _ = _ := div_one _
  exact hu.trans (mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le)

/-- A generic positive-power Dirichlet estimate up to the full principal angle. -/
lemma weighted_dirichlet_upper_pi {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    (∫ θ : ℝ in (0 : ℝ)..Real.pi, θ ^ α * ‖dirichletKernel n θ‖ ^ 2) ≤
      (1 / (1 + α) + Real.pi ^ 2 / (1 - α)) * (n : ℝ) ^ (1 - α) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcutpos : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnpos
  have hcut : 1 / (n : ℝ) ≤ Real.pi :=
    ((div_le_one hnpos).mpr hn1).trans (by linarith [Real.pi_gt_three])
  have hi (a b : ℝ) := intervalIntegrable_weighted_dirichlet (by linarith : -1 < α) n a b
  have hsmall : (∫ θ : ℝ in (0 : ℝ)..(1 / (n : ℝ)), θ ^ α * ‖dirichletKernel n θ‖ ^ 2) ≤
      (n : ℝ) ^ (1 - α) / (1 + α) := by
    rw [← dirichlet_denominator_small_integral hα0 hnpos, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hcutpos.le (hi _ _)
      ((intervalIntegrable_positive_power hα0 _).const_mul _)
    intro θ hθ
    have hs := pow_le_pow_left₀ (norm_nonneg _) (norm_dirichletKernel_le n θ) 2
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hθ.1 α)
  have hitail : IntervalIntegrable (fun θ : ℝ => θ ^ (α - 2)) volume (1 / (n : ℝ)) Real.pi :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr (Set.notMem_uIcc_of_lt hcutpos Real.pi_pos))
  have htail : (∫ θ : ℝ in (1 / (n : ℝ))..Real.pi, θ ^ α * ‖dirichletKernel n θ‖ ^ 2) ≤
      Real.pi ^ 2 * (∫ θ : ℝ in (1 / (n : ℝ))..Real.pi, θ ^ (α - 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hcut (hi _ _) (hitail.const_mul _)
    intro θ hθ
    have hpos := hcutpos.trans_le hθ.1
    have hnθ : ‖dirichletKernel n θ‖ ≤ Real.pi / θ := by
      simpa only [abs_of_pos hpos] using norm_dirichletKernel_le_pi_div (n := n) (θ := θ)
        (by simpa only [abs_of_pos hpos] using hpos)
        (by simpa only [abs_of_pos hpos] using hθ.2)
    calc
      _ ≤ θ ^ α * (Real.pi / θ) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hnθ 2) (Real.rpow_nonneg hpos.le _)
      _ = _ := by rw [Real.rpow_sub hpos, Real.rpow_two, div_pow]; ring
  have hexact : (∫ θ : ℝ in (1 / (n : ℝ))..Real.pi, θ ^ (α - 2)) =
      ((n : ℝ) ^ (1 - α) - Real.pi ^ (α - 1)) / (1 - α) := by
    rw [integral_rpow (Or.inr ⟨by linarith, Set.notMem_uIcc_of_lt hcutpos Real.pi_pos⟩)]
    have he : α - 2 + 1 = α - 1 := by ring
    rw [he, one_div, ← Real.rpow_neg_eq_inv_rpow, show -(α - 1) = 1 - α by ring]
    field_simp [show 1 - α ≠ 0 by linarith, show α - 1 ≠ 0 by linarith]
    ring
  have htailint : (∫ θ : ℝ in (1 / (n : ℝ))..Real.pi, θ ^ (α - 2)) ≤
      (n : ℝ) ^ (1 - α) / (1 - α) := by
    rw [hexact]
    exact div_le_div_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg Real.pi_pos.le _)) (by linarith)
  calc
    _ = (∫ θ : ℝ in (0 : ℝ)..(1 / (n : ℝ)), θ ^ α * ‖dirichletKernel n θ‖ ^ 2) +
        (∫ θ : ℝ in (1 / (n : ℝ))..Real.pi, θ ^ α * ‖dirichletKernel n θ‖ ^ 2) :=
      (intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)).symm
    _ ≤ (n : ℝ) ^ (1 - α) / (1 + α) + Real.pi ^ 2 * ((n : ℝ) ^ (1 - α) / (1 - α)) :=
      add_le_add hsmall (htail.trans (mul_le_mul_of_nonneg_left htailint (sq_nonneg _)))
    _ = _ := by ring

lemma weighted_dirichlet_abs_integrable {α : ℝ} (hα0 : 0 < α) (n : ℕ) :
    IntervalIntegrable (fun θ : ℝ => |θ| ^ α * ‖dirichletKernel n θ‖ ^ 2)
      volume (-Real.pi) Real.pi := by
  have hi : IntervalIntegrable (fun θ : ℝ => |θ| ^ α) volume (-Real.pi) Real.pi := by
    simpa only [neg_neg] using intervalIntegrable_abs_singular_power
      (a := -α) (by linarith) Real.pi_pos
  exact hi.mul_continuousOn ((continuous_dirichletKernel n).norm.pow 2).continuousOn

lemma weighted_dirichlet_abs_upper {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    (∫ θ : ℝ in (-Real.pi)..Real.pi, |θ| ^ α * ‖dirichletKernel n θ‖ ^ 2) ≤
      (2 * (1 / (1 + α) + Real.pi ^ 2 / (1 - α))) * (n : ℝ) ^ (1 - α) := by
  let f : ℝ → ℝ := fun θ => |θ| ^ α * ‖dirichletKernel n θ‖ ^ 2
  have hi := weighted_dirichlet_abs_integrable hα0 n
  have hi₁ : IntervalIntegrable f volume (-Real.pi) 0 := hi.mono_set (by
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
      Set.uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ 0)]
    exact Set.Icc_subset_Icc le_rfl Real.pi_pos.le)
  have hi₂ : IntervalIntegrable f volume 0 Real.pi := hi.mono_set (by
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
      Set.uIcc_of_le Real.pi_pos.le]
    exact Set.Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl)
  have hneg : (∫ θ : ℝ in (-Real.pi)..0, f θ) = ∫ θ : ℝ in (0 : ℝ)..Real.pi, f θ := by
    have hsub := intervalIntegral.integral_comp_neg (a := 0) (b := Real.pi) f
    simp only [neg_zero] at hsub
    rw [← hsub]
    apply intervalIntegral.integral_congr
    intro θ _
    simp [f]
  have hpos : (∫ θ : ℝ in (0 : ℝ)..Real.pi, f θ) =
      ∫ θ : ℝ in (0 : ℝ)..Real.pi, θ ^ α * ‖dirichletKernel n θ‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le Real.pi_pos.le] at hθ
    simp [f, abs_of_nonneg hθ.1]
  change (∫ θ : ℝ in (-Real.pi)..Real.pi, f θ) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂, hneg, hpos]
  have hb := weighted_dirichlet_upper_pi hα0 hα1 hn
  nlinarith

/-- The numerator lower constant is positive and depends only on α. -/
def sourceDirichletLowerConstant (α : ℝ) : ℝ :=
  Real.exp (-2 * sourceWeightCorrectionBound α) / (4 * (1 - α))

lemma sourceDirichletLowerConstant_pos {α : ℝ} (hα1 : α < 1) :
    0 < sourceDirichletLowerConstant α := by
  unfold sourceDirichletLowerConstant
  exact div_pos (Real.exp_pos _) (by linarith)

/-- Full-circle numerator growth for the actual principal-power weight. -/
theorem source_dirichlet_numerator_lower {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    sourceDirichletLowerConstant α * (n : ℝ) ^ (1 + α) ≤
      ∫ θ : ℝ in (-Real.pi)..Real.pi, sourceAngularWeight α θ * ‖dirichletKernel n θ‖ ^ 2 := by
  have hcompare : Real.exp (-2 * sourceWeightCorrectionBound α) *
      (∫ θ : ℝ in (0 : ℝ)..1, θ ^ (-α) * ‖dirichletKernel n θ‖ ^ 2) ≤
      ∫ θ : ℝ in (0 : ℝ)..1, sourceAngularWeight α θ * ‖dirichletKernel n θ‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one
      ((intervalIntegrable_weighted_dirichlet (by linarith : -1 < -α) n 0 1).const_mul _)
      (sourceAngularWeight_kernel_integrable hα0 hα1 n 0 1)
    intro θ hθ
    have hw := sourceAngularWeight_lower_central (θ := θ) hα0 hα1
      (by simpa only [abs_of_pos hθ.1] using hθ.1)
      (by simpa only [abs_of_pos hθ.1] using hθ.2.le)
    rw [abs_of_pos hθ.1] at hw
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hw (sq_nonneg ‖dirichletKernel n θ‖)
  have hfull : (∫ θ : ℝ in (0 : ℝ)..1, sourceAngularWeight α θ * ‖dirichletKernel n θ‖ ^ 2) ≤
      ∫ θ : ℝ in (-Real.pi)..Real.pi, sourceAngularWeight α θ * ‖dirichletKernel n θ‖ ^ 2 := by
    exact intervalIntegral.integral_mono_interval (by linarith [Real.pi_pos]) zero_le_one
      (by linarith [Real.pi_gt_three]) (ae_of_all _ fun θ =>
        mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sourceAngularWeight_kernel_integrable hα0 hα1 n _ _)
  calc
    _ = Real.exp (-2 * sourceWeightCorrectionBound α) *
        ((n : ℝ) ^ (1 + α) / (4 * (1 - α))) := by unfold sourceDirichletLowerConstant; ring
    _ ≤ Real.exp (-2 * sourceWeightCorrectionBound α) *
        (∫ θ : ℝ in (0 : ℝ)..1, θ ^ (-α) * ‖dirichletKernel n θ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (weighted_dirichlet_numerator_lower hα0 hα1 hn) (Real.exp_pos _).le
    _ ≤ _ := hcompare.trans hfull

def sourceDirichletUpperConstant (α : ℝ) : ℝ :=
  Real.exp (2 * sourceWeightCorrectionBound α) *
      (2 * (1 / (1 + α) + Real.pi ^ 2 / (1 - α))) +
    Real.pi ^ 2 * ∫ θ : ℝ in (-Real.pi)..Real.pi, sourceReflectedWeight α θ

lemma sourceReflectedWeight_integral_nonneg (α : ℝ) :
    0 ≤ ∫ θ : ℝ in (-Real.pi)..Real.pi, sourceReflectedWeight α θ :=
  intervalIntegral.integral_nonneg_of_forall (by linarith [Real.pi_pos]) fun θ => sq_nonneg _

lemma sourceDirichletUpperConstant_pos {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 < sourceDirichletUpperConstant α := by
  unfold sourceDirichletUpperConstant
  apply add_pos_of_pos_of_nonneg
  · have h₁ : 0 < 1 + α := by linarith
    have h₂ : 0 < 1 - α := by linarith
    positivity
  · exact mul_nonneg (sq_nonneg _) (sourceReflectedWeight_integral_nonneg α)

/-- A central vanishing weight plus an integrable remainder bounds the whole
reflected-weight Dirichlet integral uniformly in the degree. -/
theorem source_dirichlet_denominator_upper {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    (∫ θ : ℝ in (-Real.pi)..Real.pi, sourceReflectedWeight α θ * ‖dirichletKernel n θ‖ ^ 2) ≤
      sourceDirichletUpperConstant α * (n : ℝ) ^ (1 - α) := by
  let K := Real.exp (2 * sourceWeightCorrectionBound α)
  have hK : 0 < K := Real.exp_pos _
  have hmajor : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
      sourceReflectedWeight α θ * ‖dirichletKernel n θ‖ ^ 2 ≤
      K * (|θ| ^ α * ‖dirichletKernel n θ‖ ^ 2) + Real.pi ^ 2 * sourceReflectedWeight α θ := by
    intro θ hθ
    have hw : 0 ≤ sourceReflectedWeight α θ := sq_nonneg _
    by_cases hcentral : |θ| ≤ 1
    · have hh := mul_le_mul_of_nonneg_right (sourceReflectedWeight_upper_central hα0 hα1 hcentral)
        (sq_nonneg ‖dirichletKernel n θ‖)
      dsimp [K]
      nlinarith [mul_nonneg (sq_nonneg Real.pi) hw]
    · have ha : 1 < |θ| := lt_of_not_ge hcentral
      have hnorm : ‖dirichletKernel n θ‖ ≤ Real.pi := by
        apply (norm_dirichletKernel_le_pi_div (n := n) (by linarith : 0 < |θ|)
          (abs_le.mpr hθ)).trans
        exact (div_le_self Real.pi_pos.le ha.le)
      have hh := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hw
      have hother : 0 ≤ K * (|θ| ^ α * ‖dirichletKernel n θ‖ ^ 2) := by positivity
      nlinarith
  have hi₁ := (weighted_dirichlet_abs_integrable hα0 n).const_mul K
  have hi₂ := (sourceReflectedWeight_intervalIntegrable hα0 hα1 (-Real.pi) Real.pi).const_mul (Real.pi ^ 2)
  have hb := intervalIntegral.integral_mono_on (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)
    (sourceReflectedWeight_kernel_integrable hα0 hα1 n _ _) (hi₁.add hi₂) hmajor
  rw [intervalIntegral.integral_add hi₁ hi₂, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hb
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (1 - α) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by linarith)
  have hV := mul_nonneg (sq_nonneg Real.pi) (sourceReflectedWeight_integral_nonneg α)
  have hscale := mul_le_mul_of_nonneg_left hpow hV
  have hkernel := mul_le_mul_of_nonneg_left (weighted_dirichlet_abs_upper hα0 hα1 hn) hK.le
  unfold sourceDirichletUpperConstant
  dsimp [K] at hb hkernel
  nlinarith

lemma dirichletKernel_periodic (n : ℕ) : Function.Periodic (dirichletKernel n) (2 * Real.pi) := by
  intro θ
  change (∑ j ∈ Finset.range n, sourceCircle (θ + 2 * Real.pi) ^ j) =
    ∑ j ∈ Finset.range n, sourceCircle θ ^ j
  rw [sourceCircle_periodic θ]

/-- The shifted Dirichlet polynomial is precisely the alternating coefficient
vector evaluated on the unit circle. -/
lemma dirichletKernel_add_pi_eq_alternating (n : ℕ) (θ : ℝ) :
    dirichletKernel n (θ + Real.pi) =
      ∑ j : Fin n, (-1 : ℂ) ^ j.val * sourceCircle θ ^ j.val := by
  rw [dirichletKernel_eq_sum_fin]
  change (∑ j : Fin n, sourceCircle (θ + Real.pi) ^ j.val) = _
  apply Finset.sum_congr rfl
  intro j _
  rw [sourceCircle_add_pi, neg_pow]

lemma sourceAngularWeight_alternating_kernel_integrable {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun θ => sourceAngularWeight α θ *
      ‖dirichletKernel n (θ + Real.pi)‖ ^ 2) volume a b :=
  (sourceAngularWeight_intervalIntegrable hα0 hα1 a b).mul_continuousOn
    (((continuous_dirichletKernel n).comp (continuous_id.add_const Real.pi)).norm.pow 2).continuousOn

lemma source_dirichlet_alternating_integrable {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun θ =>
      ‖sourceWeightFactor α (sourceCircle θ) *
        (∑ j : Fin n, (-1 : ℂ) ^ j.val * sourceCircle θ ^ j.val)‖ ^ 2) volume a b := by
  simpa only [norm_mul, mul_pow, ← dirichletKernel_add_pi_eq_alternating,
    sourceAngularWeight] using sourceAngularWeight_alternating_kernel_integrable hα0 hα1 n a b

lemma periodic_fullCircle_integral_shift (f : ℝ → ℝ)
    (hf : Function.Periodic f (2 * Real.pi)) (s : ℝ) :
    (∫ θ : ℝ in (-Real.pi)..Real.pi, f (θ + s)) =
      ∫ θ : ℝ in (-Real.pi)..Real.pi, f θ := by
  rw [intervalIntegral.integral_comp_add_right]
  convert hf.intervalIntegral_add_eq (-Real.pi + s) (-Real.pi) using 1 <;> congr 1 <;> ring

/-- Shifting by a half-turn moves the alternating signs into the weight. -/
theorem source_dirichlet_alternating_integral_eq (α : ℝ) (n : ℕ) :
    (∫ θ : ℝ in (-Real.pi)..Real.pi,
      sourceAngularWeight α θ * ‖dirichletKernel n (θ + Real.pi)‖ ^ 2) =
      ∫ θ : ℝ in (-Real.pi)..Real.pi,
        sourceReflectedWeight α θ * ‖dirichletKernel n θ‖ ^ 2 := by
  let f : ℝ → ℝ := fun θ => sourceAngularWeight α θ * ‖dirichletKernel n (θ + Real.pi)‖ ^ 2
  have hperiod : Function.Periodic f (2 * Real.pi) := by
    intro θ
    dsimp [f]
    rw [sourceAngularWeight_periodic α θ,
      show θ + 2 * Real.pi + Real.pi = (θ + Real.pi) + 2 * Real.pi by ring,
      dirichletKernel_periodic n]
  have hshift : ∀ θ, f (θ + Real.pi) = sourceReflectedWeight α θ * ‖dirichletKernel n θ‖ ^ 2 := by
    intro θ
    dsimp [f]
    rw [← sourceReflectedWeight_eq_shift,
      show θ + Real.pi + Real.pi = θ + 2 * Real.pi by ring, dirichletKernel_periodic n]
  change (∫ θ : ℝ in (-Real.pi)..Real.pi, f θ) = _
  rw [← periodic_fullCircle_integral_shift f hperiod Real.pi]
  simp only [hshift]

/-- The explicit gain is uniform over all positive integer degrees. Both
integrals involve the actual source weight, and all their integrability has
been proved above. -/
theorem source_dirichlet_reflected_gain {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℕ, 1 ≤ n →
      (d * (n : ℝ) ^ α) ^ 2 *
        (∫ θ : ℝ in (-Real.pi)..Real.pi, sourceReflectedWeight α θ * ‖dirichletKernel n θ‖ ^ 2) ≤
          ∫ θ : ℝ in (-Real.pi)..Real.pi, sourceAngularWeight α θ * ‖dirichletKernel n θ‖ ^ 2 := by
  let A := sourceDirichletLowerConstant α
  let C := sourceDirichletUpperConstant α
  have hA : 0 < A := sourceDirichletLowerConstant_pos hα1
  have hC : 0 < C := sourceDirichletUpperConstant_pos hα0 hα1
  let d := Real.sqrt (A / C)
  have hd : 0 < d := Real.sqrt_pos.mpr (div_pos hA hC)
  refine ⟨d, hd, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpower : ((n : ℝ) ^ α) ^ 2 * (n : ℝ) ^ (1 - α) = (n : ℝ) ^ (1 + α) := by
    rw [← Real.rpow_mul_natCast hnpos.le, ← Real.rpow_add hnpos]
    congr 1
    norm_num
    ring
  have hscale : (d * (n : ℝ) ^ α) ^ 2 * (C * (n : ℝ) ^ (1 - α)) =
      A * (n : ℝ) ^ (1 + α) := by
    rw [mul_pow]
    dsimp only [d]
    rw [Real.sq_sqrt (div_pos hA hC).le]
    calc
      _ = A * (((n : ℝ) ^ α) ^ 2 * (n : ℝ) ^ (1 - α)) := by field_simp
      _ = _ := by rw [hpower]
  calc
    _ ≤ (d * (n : ℝ) ^ α) ^ 2 * (C * (n : ℝ) ^ (1 - α)) :=
      mul_le_mul_of_nonneg_left (source_dirichlet_denominator_upper hα0 hα1 hn) (sq_nonneg _)
    _ = _ := hscale
    _ ≤ _ := source_dirichlet_numerator_lower hα0 hα1 hn

/-- The source's explicit alternating coefficient vector has the required
weighted sign gain, with no operator-norm attainment assumption. -/
theorem source_dirichlet_alternating_gain {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℕ, 1 ≤ n →
      (d * (n : ℝ) ^ α) ^ 2 *
        (∫ θ : ℝ in (-Real.pi)..Real.pi,
          ‖sourceWeightFactor α (sourceCircle θ) *
            (∑ j : Fin n, (-1 : ℂ) ^ j.val * sourceCircle θ ^ j.val)‖ ^ 2) ≤
        ∫ θ : ℝ in (-Real.pi)..Real.pi,
          ‖sourceWeightFactor α (sourceCircle θ) * dirichletKernel n θ‖ ^ 2 := by
  obtain ⟨d, hd, hgain⟩ := source_dirichlet_reflected_gain hα0 hα1
  refine ⟨d, hd, ?_⟩
  intro n hn
  have h := hgain n hn
  rw [← source_dirichlet_alternating_integral_eq] at h
  simpa only [norm_mul, mul_pow, ← dirichletKernel_add_pi_eq_alternating, sourceAngularWeight] using h

/-- Set-integral form for direct use with the angular `L²` realization. -/
theorem source_dirichlet_alternating_gain_set {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℕ, 1 ≤ n →
      (d * (n : ℝ) ^ α) ^ 2 *
        (∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi,
          ‖sourceWeightFactor α (sourceCircle θ) *
            (∑ j : Fin n, (-1 : ℂ) ^ j.val * sourceCircle θ ^ j.val)‖ ^ 2) ≤
        ∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi,
          ‖sourceWeightFactor α (sourceCircle θ) * dirichletKernel n θ‖ ^ 2 := by
  obtain ⟨d, hd, hgain⟩ := source_dirichlet_alternating_gain hα0 hα1
  refine ⟨d, hd, ?_⟩
  intro n hn
  simpa only [intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
    integral_Icc_eq_integral_Ioc] using hgain n hn

end ProofProject
