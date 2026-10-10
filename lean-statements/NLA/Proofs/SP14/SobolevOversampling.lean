import NLA.Proofs.SP14.BaseJetRealSolve
import Mathlib.Analysis.SpecificLimits.Normed

/-!
The exact operator-algebra core of the source's Sobolev oversampling
lemma. The concrete weighted-sequence Sobolev instantiation and the
background-dependent inverse estimates remain separate obligations.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Ring

namespace NLA.Proofs.SP14

variable {Hs Hr : Type*}
  [NormedAddCommGroup Hs] [NormedSpace ℂ Hs] [CompleteSpace Hs]
  [NormedAddCommGroup Hr] [NormedSpace ℂ Hr]

noncomputable def oversamplingError
    (As Bs : Hs →L[ℂ] Hs) (P : ℕ → Hs →L[ℂ] Hs) (h q : ℕ) :
    Hs →L[ℂ] Hs :=
  P h * As * (1 - P q) * Bs * P h

noncomputable def oversamplingRightInverse
    (As Bs : Hs →L[ℂ] Hs) (P : ℕ → Hs →L[ℂ] Hs) (h q : ℕ) :
    Hs →L[ℂ] Hs :=
  P q * Bs * P h * (1 - oversamplingError As Bs P h q)⁻¹ʳ

/-- Abstract operator form of the source's Sobolev oversampling lemma. The weighted
sequence-space estimates and the background inverse bounds are explicit inputs. -/
theorem sobolevOversampling
    (τ : ℝ) (_hτ : 0 < τ) (h q : ℕ) (_hhq : h ≤ q)
    (incl : Hr →L[ℂ] Hs)
    (As Bs : Hs →L[ℂ] Hs) (Ar Br : Hr →L[ℂ] Hr)
    (P : ℕ → Hs →L[ℂ] Hs) (Lh : Hs →L[ℂ] Hr)
    (Ms Ks Kr : ℝ) (hMs : 0 ≤ Ms) (hKs : 0 ≤ Ks) (hKr : 0 ≤ Kr)
    (hAsBs : As * Bs = 1) (_hBsAs : Bs * As = 1)
    (_hArBr : Ar * Br = 1) (_hBrAr : Br * Ar = 1)
    (_hcompatA : incl.comp Ar = As.comp incl)
    (hcompatB : incl.comp Br = Bs.comp incl)
    (hPidem : ∀ n, P n * P n = P n)
    (hPnorm : ∀ n, ‖P n‖ ≤ 1)
    (hLift : incl.comp Lh = P h)
    (hTail : ∀ x : Hr, ‖((1 - P q).comp incl) x‖ ≤
      ((q + 1 : ℕ) : ℝ) ^ (-τ) * ‖x‖)
    (hBand : ∀ y : Hs, ‖Lh y‖ ≤ (h : ℝ) ^ τ * ‖P h y‖)
    (hAs : ‖As‖ ≤ Ms) (hBs : ‖Bs‖ ≤ Ks) (hBr : ‖Br‖ ≤ Kr)
    (hsmall : Ms * Kr * ((h : ℝ) / (q + 1 : ℕ)) ^ τ < 1) :
    let E := oversamplingError As Bs P h q
    let R := oversamplingRightInverse As Bs P h q
    ‖E‖ ≤ Ms * Kr * ((h : ℝ) / (q + 1 : ℕ)) ^ τ ∧
    IsUnit (1 - E) ∧
    P q * R = R ∧
    P h * As * P q * R = P h ∧
    ‖R‖ ≤ Ks / (1 - Ms * Kr * ((h : ℝ) / (q + 1 : ℕ)) ^ τ) := by
  let ε : ℝ := Ms * Kr * ((h : ℝ) / (q + 1 : ℕ)) ^ τ
  let E : Hs →L[ℂ] Hs := oversamplingError As Bs P h q
  let R : Hs →L[ℂ] Hs := oversamplingRightInverse As Bs P h q
  have hεnonneg : 0 ≤ ε := by dsimp [ε]; positivity
  have hpow : 0 ≤ (h : ℝ) ^ τ := Real.rpow_nonneg (by positivity) _
  have htailpow : 0 ≤ ((q + 1 : ℕ) : ℝ) ^ (-τ) :=
    Real.rpow_nonneg (by positivity) _
  have hTailNorm : ‖(1 - P q).comp incl‖ ≤ ((q + 1 : ℕ) : ℝ) ^ (-τ) :=
    ((1 - P q).comp incl).opNorm_le_bound htailpow hTail
  have hLiftNorm : ‖Lh‖ ≤ (h : ℝ) ^ τ := by
    apply Lh.opNorm_le_bound hpow
    intro y
    have hPy : ‖P h y‖ ≤ ‖y‖ := calc
      ‖P h y‖ ≤ ‖P h‖ * ‖y‖ := (P h).le_opNorm y
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (hPnorm h) (norm_nonneg y)
      _ = ‖y‖ := one_mul _
    exact (hBand y).trans (mul_le_mul_of_nonneg_left hPy hpow)
  have hBPy (y : Hs) : Bs (P h y) = incl (Br (Lh y)) := by
    calc
      Bs (P h y) = Bs (incl (Lh y)) := by rw [← hLift]; rfl
      _ = incl (Br (Lh y)) := by
        have := congrArg (fun f : Hr →L[ℂ] Hs => f (Lh y)) hcompatB.symm
        simpa only [ContinuousLinearMap.comp_apply] using this
  have hEeq : E = (P h).comp (As.comp (((1 - P q).comp incl).comp (Br.comp Lh))) := by
    ext y
    simp only [E, oversamplingError, ContinuousLinearMap.comp_apply, mul_apply_eq_comp]
    rw [hBPy]
  have hE : ‖E‖ ≤ ε := by
    rw [hEeq]
    calc
      ‖(P h).comp (As.comp (((1 - P q).comp incl).comp (Br.comp Lh)))‖
          ≤ ‖P h‖ * ‖As.comp (((1 - P q).comp incl).comp (Br.comp Lh))‖ :=
            (P h).opNorm_comp_le _
      _ ≤ ‖P h‖ * (‖As‖ * ‖((1 - P q).comp incl).comp (Br.comp Lh)‖) := by
        gcongr
        exact As.opNorm_comp_le _
      _ ≤ ‖P h‖ * (‖As‖ * (‖(1 - P q).comp incl‖ * ‖Br.comp Lh‖)) := by
        gcongr
        exact ((1 - P q).comp incl).opNorm_comp_le _
      _ ≤ ‖P h‖ * (‖As‖ * (‖(1 - P q).comp incl‖ * (‖Br‖ * ‖Lh‖))) := by
        gcongr
        exact Br.opNorm_comp_le _
      _ ≤ 1 * (Ms * (((q + 1 : ℕ) : ℝ) ^ (-τ) * (Kr * ((h : ℝ) ^ τ)))) := by
        gcongr
        exact hPnorm h
      _ = ε := by
        dsimp [ε]
        rw [Real.div_rpow (by positivity : (0:ℝ) ≤ h) (by positivity : (0:ℝ) ≤ (q+1:ℕ)) τ]
        rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ (q+1:ℕ))]
        ring
  have hElt : ‖E‖ < 1 := lt_of_le_of_lt hE hsmall
  have hunit : IsUnit (1 - E) := isUnit_one_sub_of_norm_lt_one hElt
  let U : Hs →L[ℂ] Hs := (1 - E)⁻¹ʳ
  have hInv : (1 - E) * U = 1 := Ring.mul_inverse_cancel _ hunit
  have hUeq : U = 1 + E * U := by
    calc
      U = (1 - E) * U + E * U := by noncomm_ring
      _ = 1 + E * U := by rw [hInv]
  have hOneNorm : ‖(1 : Hs →L[ℂ] Hs)‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℂ Hs‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  have hδ : 0 < 1 - ε := sub_pos.mpr hsmall
  have hUnorm : ‖U‖ ≤ (1 - ε)⁻¹ := by
    have hbound : ‖U‖ ≤ 1 + ε * ‖U‖ := calc
      ‖U‖ = ‖1 + E * U‖ := congrArg norm hUeq
      _ ≤ ‖(1 : Hs →L[ℂ] Hs)‖ + ‖E * U‖ := norm_add_le _ _
      _ ≤ 1 + ε * ‖U‖ := by
        have hmul := norm_mul_le E U
        have hεmul := mul_le_mul_of_nonneg_right hE (norm_nonneg U)
        linarith
    have haux : ‖U‖ ≤ 1 / (1 - ε) := (le_div_iff₀ hδ).2 (by nlinarith)
    simpa only [one_div] using haux
  have hPqR : P q * R = R := by
    dsimp [R, oversamplingRightInverse]
    calc
      P q * (P q * Bs * P h * U) = (P q * P q) * Bs * P h * U := by noncomm_ring
      _ = P q * Bs * P h * U := by rw [hPidem q]
  have hPE : P h * E = E := by
    dsimp [E, oversamplingError]
    calc
      P h * (P h * As * (1 - P q) * Bs * P h) =
          (P h * P h) * As * (1 - P q) * Bs * P h := by noncomm_ring
      _ = P h * As * (1 - P q) * Bs * P h := by rw [hPidem h]
  have hAident : P h * As * P q * Bs * P h = P h - E := by
    calc
      P h * As * P q * Bs * P h = P h * As * Bs * P h - E := by
        dsimp [E, oversamplingError]
        noncomm_ring
      _ = P h - E := by
        rw [mul_assoc (P h) As Bs, hAsBs, mul_one, hPidem h]
  have hRight : P h * As * P q * R = P h := by
    dsimp [R, oversamplingRightInverse]
    calc
      P h * As * P q * (P q * Bs * P h * U) =
          (P h * As * P q * Bs * P h) * U := by
            calc
              _ = P h * As * (P q * P q) * Bs * P h * U := by noncomm_ring
              _ = _ := by rw [hPidem q]
      _ = (P h - E) * U := by rw [hAident]
      _ = (P h * (1 - E)) * U := by rw [mul_sub, mul_one, hPE]
      _ = P h := by rw [mul_assoc, hInv, mul_one]
  have hRnorm : ‖R‖ ≤ Ks / (1 - ε) := by
    have hRle : ‖R‖ ≤ ‖P q‖ * ‖Bs‖ * ‖P h‖ * ‖U‖ := by
      dsimp [R, oversamplingRightInverse]
      calc
        ‖P q * Bs * P h * U‖ ≤ ‖P q * Bs * P h‖ * ‖U‖ := norm_mul_le _ _
        _ ≤ (‖P q * Bs‖ * ‖P h‖) * ‖U‖ := by
          gcongr
          exact norm_mul_le _ _
        _ ≤ (‖P q‖ * ‖Bs‖ * ‖P h‖) * ‖U‖ := by
          gcongr
          exact norm_mul_le _ _
    calc
      ‖R‖ ≤ ‖P q‖ * ‖Bs‖ * ‖P h‖ * ‖U‖ := hRle
      _ ≤ 1 * Ks * 1 * (1 - ε)⁻¹ := by
        gcongr <;> first | exact hPnorm q | exact hBs | exact hPnorm h
      _ = Ks / (1 - ε) := by ring
  dsimp
  exact ⟨hE, hunit, hPqR, hRight, hRnorm⟩

end NLA.Proofs.SP14
