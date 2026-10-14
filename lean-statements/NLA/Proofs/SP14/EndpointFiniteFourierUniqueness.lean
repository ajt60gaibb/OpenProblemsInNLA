import NLA.Proofs.SP14.EndpointFiniteRealizationNegative
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
Continuous uniqueness for the frozen SP-14 Fourier coefficient, including
its exact real-interval normalization. The finite pointwise endpoint theorem
is a separate gate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

open NLA.Statements.SP14 MeasureTheory

private instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private theorem frozen_fourier_eq_addCircle
    (f : Circle → ℂ) (p : ℤ) :
    FourierCoefficient f p =
      fourierCoeff
        (fun x : AddCircle (2 * Real.pi) => f (AddCircle.homeomorphCircle' x)) p := by
  rw [fourierCoeff_eq_intervalIntegral _ p 0]
  unfold FourierCoefficient
  simp only [zero_add, smul_eq_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  change f (Circle.exp t) * Complex.exp (-((p : ℂ) * Complex.I * (t : ℂ))) =
    fourier (-p) (t : AddCircle (2 * Real.pi)) *
      f (AddCircle.homeomorphCircle' (t : AddCircle (2 * Real.pi)))
  rw [AddCircle.homeomorphCircle'_apply_mk, fourier_coe_apply]
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hexp :
      2 * (Real.pi : ℂ) * Complex.I * (-(p : ℂ)) * (t : ℂ) /
          (((2 : ℝ) : ℂ) * (Real.pi : ℂ)) =
        -((p : ℂ) * Complex.I * (t : ℂ)) := by
    simp only [Complex.ofReal_ofNat]
    field_simp
  simp only [Int.cast_neg, Complex.ofReal_mul]
  rw [hexp]
  ring

/-- Continuous circle functions are determined by every coefficient of the
original normalized interval integral, with both positive and negative modes. -/
theorem continuous_eq_of_forall_FourierCoefficient_eq
    (f g : Circle → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hcoeff : ∀ p : ℤ, FourierCoefficient f p = FourierCoefficient g p) :
    f = g := by
  let μ : Measure (AddCircle (2 * Real.pi)) := AddCircle.haarAddCircle
  let F : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨fun x => f (AddCircle.homeomorphCircle' x),
      hf.comp AddCircle.homeomorphCircle'.continuous⟩
  let G : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨fun x => g (AddCircle.homeomorphCircle' x),
      hg.comp AddCircle.homeomorphCircle'.continuous⟩
  have hFC : ∀ p : ℤ, fourierCoeff (F : AddCircle (2 * Real.pi) → ℂ) p =
      fourierCoeff (G : AddCircle (2 * Real.pi) → ℂ) p := by
    intro p
    exact (frozen_fourier_eq_addCircle f p).symm.trans
      ((hcoeff p).trans (frozen_fourier_eq_addCircle g p))
  have hLp :
      ContinuousMap.toLp (E := ℂ) (2 : ENNReal) μ ℂ F =
        ContinuousMap.toLp (E := ℂ) (2 : ENNReal) μ ℂ G := by
    apply (fourierBasis (T := 2 * Real.pi)).repr.injective
    apply lp.ext
    funext p
    rw [fourierBasis_repr, fourierBasis_repr]
    have hFa := fourierCoeff_congr_ae
      (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal)) (μ := μ) F)
    have hGa := fourierCoeff_congr_ae
      (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal)) (μ := μ) G)
    exact (congrFun hFa p).trans ((hFC p).trans (congrFun hGa p).symm)
  have hFG : F = G :=
    (ContinuousMap.toLp_inj (𝕜 := ℂ) (p := (2 : ENNReal)) (μ := μ)).mp hLp
  funext z
  have h := congrArg (fun H : C(AddCircle (2 * Real.pi), ℂ) =>
    H (AddCircle.homeomorphCircle'.symm z)) hFG
  change f (AddCircle.homeomorphCircle' (AddCircle.homeomorphCircle'.symm z)) =
    g (AddCircle.homeomorphCircle' (AddCircle.homeomorphCircle'.symm z)) at h
  simpa only [AddCircle.homeomorphCircle'.apply_symm_apply] using h

#assert_trust kernel continuous_eq_of_forall_FourierCoefficient_eq
#print axioms continuous_eq_of_forall_FourierCoefficient_eq

end NLA.Proofs.SP14
