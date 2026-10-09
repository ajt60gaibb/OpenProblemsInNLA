import ProofProject.OscillatoryNonstationary
import ProofProject.OscillatoryCriticalInterval

/-!
# The second-derivative test for complex amplitudes

The critical interval is estimated by its length. The complementary intervals
use the first-derivative estimate, including the cases where either interval
is empty. The variation of the amplitude is counted only once.
-/

noncomputable section
open MeasureTheory Set
namespace ProofProject

/-- Combine two nonstationary intervals and the interval between them. The
separation hypotheses are required only for intervals of positive length. -/
theorem norm_oscillatory_integral_le_of_critical_interval {a b c d δ C : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) (hδ : 0 < δ) (hC : 0 ≤ C)
    {A A' : ℝ → ℂ} {φ p p' : ℝ → ℝ}
    (hA : ∀ x ∈ Icc a b, HasDerivAt A (A' x) x)
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (p x) x)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (p' x) x)
    (hA' : ContinuousOn A' (Icc a b)) (hp' : ContinuousOn p' (Icc a b))
    (hleft : a < c → ∀ x ∈ Icc a c, δ ≤ |p x|)
    (hright : d < b → ∀ x ∈ Icc d b, δ ≤ |p x|)
    (hbound : ∀ x ∈ Icc a b, ‖A x‖ ≤ C)
    (hsign : (∀ x ∈ Icc a b, 0 ≤ p' x) ∨ (∀ x ∈ Icc a b, p' x ≤ 0)) :
    ‖∫ x in a..b, A x * oscillatoryExponential φ x‖ ≤
      (8 * C + ∫ x in a..b, ‖A' x‖) / δ + C * (d - c) := by
  have hab := hac.trans (hcd.trans hdb)
  have hAc : ContinuousOn A (Icc a b) := fun x hx => (hA x hx).continuousAt.continuousWithinAt
  have hec : ContinuousOn (oscillatoryExponential φ) (Icc a b) := fun x hx =>
    (oscillatoryExponential_hasDerivAt (hφ x hx)).continuousAt.continuousWithinAt
  have hF := hAc.mul hec
  have hsub {u v : ℝ} (hau : a ≤ u) (hvb : v ≤ b) : Icc u v ⊆ Icc a b :=
    Icc_subset_Icc hau hvb
  have hfi {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
      IntervalIntegrable (fun x => A x * oscillatoryExponential φ x) volume u v :=
    (hF.mono (hsub hau hvb)).intervalIntegrable_of_Icc huv
  have hvi {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
      IntervalIntegrable (fun x => ‖A' x‖) volume u v :=
    (hA'.norm.mono (hsub hau hvb)).intervalIntegrable_of_Icc huv
  have hside {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
      (hsep : u < v → ∀ x ∈ Icc u v, δ ≤ |p x|) :
      ‖∫ x in u..v, A x * oscillatoryExponential φ x‖ ≤
        (4 * C + ∫ x in u..v, ‖A' x‖) / δ := by
    rcases huv.eq_or_lt with heq | hlt
    · subst v
      simp only [intervalIntegral.integral_same, norm_zero, add_zero]
      positivity
    · apply norm_oscillatory_integral_le_first_derivative huv hδ hC
        (fun x hx => hA x (hsub hau hvb hx))
        (fun x hx => hφ x (hsub hau hvb hx))
        (fun x hx => hp x (hsub hau hvb hx))
        (hA'.mono (hsub hau hvb)) (hp'.mono (hsub hau hvb)) (hsep hlt)
        (fun x hx => hbound x (hsub hau hvb hx))
      exact hsign.imp (fun h x hx => h x (hsub hau hvb hx))
        (fun h x hx => h x (hsub hau hvb hx))
  have hmid : ‖∫ x in c..d, A x * oscillatoryExponential φ x‖ ≤ C * (d - c) := by
    simpa only [abs_of_nonneg (sub_nonneg.mpr hcd)] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := d)
        (f := fun x => A x * oscillatoryExponential φ x) (C := C) (by
          intro x hx
          rw [uIoc_of_le hcd] at hx
          simpa only [norm_mul, norm_oscillatoryExponential, mul_one] using
            hbound x ⟨hac.trans hx.1.le, hx.2.trans hdb⟩))
  have hsplit : (∫ x in a..b, A x * oscillatoryExponential φ x) =
      ((∫ x in a..c, A x * oscillatoryExponential φ x) +
      ∫ x in c..d, A x * oscillatoryExponential φ x) +
      ∫ x in d..b, A x * oscillatoryExponential φ x := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hfi le_rfl hac (hcd.trans hdb)) (hfi hac hcd hdb),
      intervalIntegral.integral_add_adjacent_intervals
      (hfi le_rfl (hac.trans hcd) hdb) (hfi (hac.trans hcd) hdb le_rfl)]
  have hvar : (∫ x in a..c, ‖A' x‖) + (∫ x in d..b, ‖A' x‖) ≤
      ∫ x in a..b, ‖A' x‖ := by
    have hsum := intervalIntegral.integral_add_adjacent_intervals
      (hvi le_rfl hac (hcd.trans hdb)) (hvi hac hcd hdb)
    have hsum' := intervalIntegral.integral_add_adjacent_intervals
      (hvi le_rfl (hac.trans hcd) hdb) (hvi (hac.trans hcd) hdb le_rfl)
    have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) hcd (fun x => norm_nonneg (A' x))
    linarith
  rw [hsplit]
  calc
    _ ≤ (‖∫ x in a..c, A x * oscillatoryExponential φ x‖ +
        ‖∫ x in c..d, A x * oscillatoryExponential φ x‖) +
        ‖∫ x in d..b, A x * oscillatoryExponential φ x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ((4 * C + ∫ x in a..c, ‖A' x‖) / δ + C * (d - c)) +
        (4 * C + ∫ x in d..b, ‖A' x‖) / δ :=
      add_le_add (add_le_add (hside le_rfl hac (hcd.trans hdb) hleft) hmid)
        (hside (hac.trans hcd) hdb le_rfl hright)
    _ = (8 * C + ((∫ x in a..c, ‖A' x‖) + ∫ x in d..b, ‖A' x‖)) / δ +
        C * (d - c) := by ring
    _ ≤ _ := add_le_add (div_le_div_of_nonneg_right (by linarith) hδ.le) le_rfl

/-- The complex-amplitude second-derivative test, for either fixed sign of the
second derivative. The variation of the amplitude has coefficient one. -/
theorem norm_oscillatory_integral_le_second_derivative {a b κ C : ℝ}
    (hab : a ≤ b) (hκ : 0 < κ) (hC : 0 ≤ C)
    {A A' : ℝ → ℂ} {φ p p' : ℝ → ℝ}
    (hA : ∀ x ∈ Icc a b, HasDerivAt A (A' x) x)
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (p x) x)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (p' x) x)
    (hA' : ContinuousOn A' (Icc a b)) (hp' : ContinuousOn p' (Icc a b))
    (hbound : ∀ x ∈ Icc a b, ‖A x‖ ≤ C)
    (hcurvature : (∀ x ∈ Icc a b, κ ≤ p' x) ∨
      (∀ x ∈ Icc a b, p' x ≤ -κ)) :
    ‖∫ x in a..b, A x * oscillatoryExponential φ x‖ ≤
      (10 * C + ∫ x in a..b, ‖A' x‖) / Real.sqrt κ := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hcuts : ∃ c d, a ≤ c ∧ c ≤ d ∧ d ≤ b ∧
      d - c ≤ 2 * Real.sqrt κ / κ ∧
      (a < c → ∀ x ∈ Icc a c, Real.sqrt κ ≤ |p x|) ∧
      (d < b → ∀ x ∈ Icc d b, Real.sqrt κ ≤ |p x|) := by
    rcases hcurvature with hpos | hneg
    · exact exists_oscillatory_critical_interval hab hκ hs hp hpos
    · obtain ⟨c, d, hac, hcd, hdb, hlen, hl, hr⟩ :=
        exists_oscillatory_critical_interval hab hκ hs
          (fun x hx => (hp x hx).neg) (fun x hx => by linarith [hneg x hx])
      exact ⟨c, d, hac, hcd, hdb, hlen,
        by simpa only [Pi.neg_apply, abs_neg] using hl, by simpa only [Pi.neg_apply, abs_neg] using hr⟩
  obtain ⟨c, d, hac, hcd, hdb, hlen, hl, hr⟩ := hcuts
  have hsign : (∀ x ∈ Icc a b, 0 ≤ p' x) ∨ (∀ x ∈ Icc a b, p' x ≤ 0) :=
    hcurvature.imp (fun h x hx => hκ.le.trans (h x hx))
      (fun h x hx => (h x hx).trans (by linarith))
  have hsquare := Real.sq_sqrt hκ.le
  have hlength : 2 * Real.sqrt κ / κ = 2 / Real.sqrt κ := by
    apply (div_eq_div_iff hκ.ne' hs.ne').mpr
    nlinarith
  calc
    _ ≤ (8 * C + ∫ x in a..b, ‖A' x‖) / Real.sqrt κ + C * (d - c) :=
      norm_oscillatory_integral_le_of_critical_interval hac hcd hdb hs hC
        hA hφ hp hA' hp' hl hr hbound hsign
    _ ≤ (8 * C + ∫ x in a..b, ‖A' x‖) / Real.sqrt κ +
        C * (2 * Real.sqrt κ / κ) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hlen hC)
    _ = _ := by rw [hlength]; ring

end ProofProject
