import NLA.Proofs.SP14.FinitePositiveWienerSize

/-!
Constant-one triangle inequality for the literal W^(9/8) Fourier-integral
size of continuous circle functions with summable weighted coefficients.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

private theorem FourierCoefficient_add_of_continuous'
    (f g : Circle → ℂ) (hf : Continuous f) (hg : Continuous g) (k : ℤ) :
    FourierCoefficient (fun s => f s + g s) k =
      FourierCoefficient f k + FourierCoefficient g k := by
  have hcf : Continuous (fun t : ℝ =>
      f (Circle.exp t) * Complex.exp (-((k : ℂ) * Complex.I * (t : ℂ)))) := by
    fun_prop
  have hcg : Continuous (fun t : ℝ =>
      g (Circle.exp t) * Complex.exp (-((k : ℂ) * Complex.I * (t : ℂ)))) := by
    fun_prop
  unfold FourierCoefficient
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add
    (hcf.intervalIntegrable 0 (2 * Real.pi))
    (hcg.intervalIntegrable 0 (2 * Real.pi))]
  ring

private theorem wienerWeight_nonneg' (k : ℤ) : 0 ≤ wienerWeight k := by
  unfold wienerWeight
  positivity

private theorem wiener_add_term_le
    (f g : Circle → ℂ) (hf : Continuous f) (hg : Continuous g) (k : ℤ) :
    wienerWeight k * ‖FourierCoefficient (fun s => f s + g s) k‖ ≤
      wienerWeight k * ‖FourierCoefficient f k‖ +
        wienerWeight k * ‖FourierCoefficient g k‖ := by
  rw [FourierCoefficient_add_of_continuous' f g hf hg]
  calc
    wienerWeight k * ‖FourierCoefficient f k + FourierCoefficient g k‖ ≤
      wienerWeight k *
        (‖FourierCoefficient f k‖ + ‖FourierCoefficient g k‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (wienerWeight_nonneg' k)
    _ = _ := by ring

theorem summable_wiener_add
    (f g : Circle → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hfs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient f k‖))
    (hgs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient g k‖)) :
    Summable (fun k : ℤ =>
      wienerWeight k *
        ‖FourierCoefficient (fun s => f s + g s) k‖) := by
  apply Summable.of_nonneg_of_le
  · intro k
    exact mul_nonneg (wienerWeight_nonneg' k) (norm_nonneg _)
  · exact wiener_add_term_le f g hf hg
  · exact hfs.add hgs

theorem weightedWienerSize_add_le
    (f g : Circle → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hfs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient f k‖))
    (hgs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient g k‖)) :
    weightedWienerSize (fun s => f s + g s) ≤
      weightedWienerSize f + weightedWienerSize g := by
  have hsum := summable_wiener_add f g hf hg hfs hgs
  unfold weightedWienerSize
  calc
    (∑' k : ℤ,
      wienerWeight k * ‖FourierCoefficient (fun s => f s + g s) k‖) ≤
      ∑' k : ℤ,
        (wienerWeight k * ‖FourierCoefficient f k‖ +
          wienerWeight k * ‖FourierCoefficient g k‖) :=
      hsum.tsum_le_tsum (wiener_add_term_le f g hf hg) (hfs.add hgs)
    _ = _ := by rw [hfs.tsum_add hgs]

#assert_trust kernel summable_wiener_add
#assert_trust kernel weightedWienerSize_add_le

end NLA.Proofs.SP14
