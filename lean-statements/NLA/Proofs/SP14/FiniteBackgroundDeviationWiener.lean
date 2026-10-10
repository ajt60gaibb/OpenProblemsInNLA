import NLA.Proofs.SP14.FiniteCorrectionSquareWiener
import NLA.Proofs.SP14.WienerShift
import NLA.Proofs.SP14.NegativeLaurentEndpointDivision
import NLA.Proofs.SP14.PositiveEndpointRatio

/-!
The literal W^(9/8) deviation bound for an actual finite endpoint-contact
background. This estimates the finite curve only; it asserts no background
operator inverse or stage closure.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

private theorem weightedWienerSize_nonneg (f : Circle → ℂ) :
    0 ≤ weightedWienerSize f := by
  unfold weightedWienerSize
  apply tsum_nonneg
  intro k
  exact mul_nonneg (by unfold wienerWeight; positivity) (norm_nonneg _)

private theorem wienerUnit_nonneg :
    0 ≤ (2 : ℝ) ^ (9 / 8 : ℝ) := by positivity

theorem finiteBackgroundCurve_deviation_wiener_of_factors
    (u v : ℕ) (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ)
    (qMinus : Fin u → ℝ) (qPlus : Fin v → ℝ)
    (hm : ∀ s : Circle,
      negativeLaurent u pMinus s =
        (1 + (s : ℂ)) * negativeLaurent u qMinus s)
    (hp : ∀ s : Circle,
      positiveLaurent v pPlus s =
        (1 + (s : ℂ)) * positiveLaurent v qPlus s) :
    Summable (fun k : ℤ => wienerWeight k *
      ‖FourierCoefficient
        (fun s : Circle => finiteBackgroundCurve u v pMinus pPlus s - (s : ℂ)) k‖) ∧
    weightedWienerSize
        (fun s : Circle => finiteBackgroundCurve u v pMinus pPlus s - (s : ℂ)) ≤
      2 * (2 : ℝ) ^ (9 / 8 : ℝ) * weightedWienerSize regularizedBaseFactor *
        (weightedWienerSize (negativeLaurent u qMinus) +
          weightedWienerSize (positiveLaurent v qPlus)) +
      (2 : ℝ) ^ (9 / 8 : ℝ) *
        (weightedWienerSize (negativeLaurent u pMinus) +
          weightedWienerSize (positiveLaurent v pPlus)) ^ 2 := by
  let F := regularizedBaseFactor
  let Qm := negativeLaurent u qMinus
  let Qp := positiveLaurent v qPlus
  let P := finiteLaurentCorrection u v pMinus pPlus
  let Tm : Circle → ℂ := fun s => F s * Qm s
  let Tp : Circle → ℂ := fun s => F s * Qp s
  let T : Circle → ℂ := fun s => Tm s + Tp s
  let Sq : Circle → ℂ := fun s => P s ^ 2
  let ST : Circle → ℂ := fun s => (s : ℂ) * T s
  let SSq : Circle → ℂ := fun s => (s : ℂ) * Sq s
  have hF : Continuous F := continuous_regularizedBaseFactor
  have hQm : Continuous Qm := continuous_negativeLaurent u qMinus
  have hQp : Continuous Qp := continuous_positiveLaurent v qPlus
  have hTm : Continuous Tm := hF.mul hQm
  have hTp : Continuous Tp := hF.mul hQp
  have hT : Continuous T := hTm.add hTp
  have hP : Continuous P := continuous_finiteLaurentCorrection u v pMinus pPlus
  have hSq : Continuous Sq := hP.pow 2
  have hST : Continuous ST := continuous_subtype_val.mul hT
  have hSSq : Continuous SSq := continuous_subtype_val.mul hSq
  have hFs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient F k‖) :=
    summable_regularizedBaseFactor_wiener
  have hTms : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient Tm k‖) :=
    summable_mul_negativeLaurent_wiener F hF hFs u qMinus
  have hTps : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient Tp k‖) :=
    summable_mul_positiveLaurent_wiener F hF hFs v qPlus
  have hTs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient T k‖) :=
    summable_wiener_add Tm Tp hTm hTp hTms hTps
  have hSqs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient Sq k‖) :=
    summable_finiteLaurentCorrection_sq_wiener u v pMinus pPlus
  have hSTs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient ST k‖) :=
    summable_wiener_mul_s T hT hTs
  have hSSqs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient SSq k‖) :=
    summable_wiener_mul_s Sq hSq hSqs
  have hdev : (fun s : Circle =>
      finiteBackgroundCurve u v pMinus pPlus s - (s : ℂ)) =
      (fun s => ST s + ST s + SSq s) := by
    funext s
    rw [finiteBackgroundCurve_deviation]
    have hpm := hm s
    have hpp := hp s
    dsimp [ST, SSq, Sq, T, Tm, Tp, F, Qm, Qp, P,
      finiteLaurentCorrection]
    rw [hpm, hpp]
    simp only [regularizedBaseFactor]
    ring
  have h2STs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient (fun s => ST s + ST s) k‖) :=
    summable_wiener_add ST ST hST hST hSTs hSTs
  constructor
  · rw [hdev]
    exact summable_wiener_add (fun s => ST s + ST s) SSq
      (hST.add hST) hSSq h2STs hSSqs
  · rw [hdev]
    have hsum := weightedWienerSize_add_le
      (fun s => ST s + ST s) SSq (hST.add hST) hSSq h2STs hSSqs
    have hdouble := weightedWienerSize_add_le ST ST hST hST hSTs hSTs
    have htm := weightedWienerSize_mul_negativeLaurent_le F hF hFs u qMinus
    have htp := weightedWienerSize_mul_positiveLaurent_le F hF hFs v qPlus
    have ht := weightedWienerSize_add_le Tm Tp hTm hTp hTms hTps
    have hst := weightedWienerSize_mul_s_le T hT hTs
    have hssq := weightedWienerSize_mul_s_le Sq hSq hSqs
    have hsq := weightedWienerSize_finiteLaurentCorrection_sq_le
      u v pMinus pPlus
    have hqm : weightedWienerSize Qm = finiteNegativeWienerSize u qMinus :=
      negativeLaurent_wiener_eq u qMinus
    have hqp : weightedWienerSize Qp = finitePositiveWienerSize v qPlus :=
      positiveLaurent_wiener_eq v qPlus
    have hTbound : weightedWienerSize T ≤
        weightedWienerSize F *
          (weightedWienerSize Qm + weightedWienerSize Qp) := by
      rw [hqm, hqp]
      nlinarith [ht, htm, htp]
    have hSTbound : weightedWienerSize ST ≤
        (2 : ℝ) ^ (9 / 8 : ℝ) * weightedWienerSize F *
          (weightedWienerSize Qm + weightedWienerSize Qp) := by
      have hh := mul_le_mul_of_nonneg_left hTbound wienerUnit_nonneg
      nlinarith [hst]
    have hSqbound : weightedWienerSize SSq ≤
        (2 : ℝ) ^ (9 / 8 : ℝ) *
          (weightedWienerSize (negativeLaurent u pMinus) +
            weightedWienerSize (positiveLaurent v pPlus)) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left hsq wienerUnit_nonneg
      nlinarith [hssq]
    nlinarith [hsum, hdouble, hSTbound, hSqbound]

theorem finiteBackgroundCurve_deviation_wiener_of_contact
    (u v : ℕ) (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ)
    (hm : negativeLaurent u pMinus (-1 : Circle) = 0)
    (hp : positiveLaurent v pPlus (-1 : Circle) = 0) :
    ∃ qMinus : Fin u → ℝ, ∃ qPlus : Fin v → ℝ,
      (∀ s : Circle,
        negativeLaurent u pMinus s =
          (1 + (s : ℂ)) * negativeLaurent u qMinus s) ∧
      (∀ s : Circle,
        positiveLaurent v pPlus s =
          (1 + (s : ℂ)) * positiveLaurent v qPlus s) ∧
      Summable (fun k : ℤ => wienerWeight k *
        ‖FourierCoefficient
          (fun s : Circle => finiteBackgroundCurve u v pMinus pPlus s - (s : ℂ)) k‖) ∧
      weightedWienerSize
          (fun s : Circle => finiteBackgroundCurve u v pMinus pPlus s - (s : ℂ)) ≤
        2 * (2 : ℝ) ^ (9 / 8 : ℝ) * weightedWienerSize regularizedBaseFactor *
          (weightedWienerSize (negativeLaurent u qMinus) +
            weightedWienerSize (positiveLaurent v qPlus)) +
        (2 : ℝ) ^ (9 / 8 : ℝ) *
          (weightedWienerSize (negativeLaurent u pMinus) +
            weightedWienerSize (positiveLaurent v pPlus)) ^ 2 := by
  obtain ⟨qMinus, _, hmf⟩ := negativeLaurent_endpoint_factor u pMinus hm
  obtain ⟨qPlus, hpf⟩ := positiveLaurent_endpoint_factor v pPlus hp
  refine ⟨qMinus, qPlus, hmf, hpf, ?_⟩
  exact finiteBackgroundCurve_deviation_wiener_of_factors
    u v pMinus pPlus qMinus qPlus hmf hpf

#assert_trust kernel finiteBackgroundCurve_deviation_wiener_of_factors
#assert_trust kernel finiteBackgroundCurve_deviation_wiener_of_contact

end NLA.Proofs.SP14
