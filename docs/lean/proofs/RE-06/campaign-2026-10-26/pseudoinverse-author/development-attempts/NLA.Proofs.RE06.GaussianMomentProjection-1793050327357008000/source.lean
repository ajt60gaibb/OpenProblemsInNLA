import NLA.Proofs.RE06.GaussianMomentNorm
import NLA.Proofs.RE06.GaussianRotation

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped InnerProductSpace

namespace NLA.Proofs.RE06.GaussianMoment

theorem coisometry_adjoint_norm_sq {p q : ℕ}
    (T : GaussianEuclid p →L[ℝ] GaussianEuclid q)
    (hT : T.comp T.adjoint = ContinuousLinearMap.id ℝ (GaussianEuclid q))
    (y : GaussianEuclid q) : ‖T.adjoint y‖ ^ 2 = ‖y‖ ^ 2 := by
  calc
    _ = ⟪T.adjoint y, T.adjoint y⟫_ℝ := (real_inner_self_eq_norm_sq _).symm
    _ = ⟪T (T.adjoint y), y⟫_ℝ := T.adjoint_inner_right _ _
    _ = ⟪y, y⟫_ℝ := by
      have hh := congrArg (fun S : GaussianEuclid q →L[ℝ] GaussianEuclid q => S y) hT
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
        congrArg (fun z => ⟪z, y⟫_ℝ) hh
    _ = _ := real_inner_self_eq_norm_sq _

theorem stdGaussian_map_coisometry {p q : ℕ}
    (T : GaussianEuclid p →L[ℝ] GaussianEuclid q)
    (hT : T.comp T.adjoint = ContinuousLinearMap.id ℝ (GaussianEuclid q)) :
    (stdGaussian (GaussianEuclid p)).map T = stdGaussian (GaussianEuclid q) := by
  apply Measure.ext_of_charFun
  ext y
  have hchar : charFun ((stdGaussian (GaussianEuclid p)).map T) y =
      charFun (stdGaussian (GaussianEuclid p)) (T.adjoint y) := by
    rw [charFun_apply, integral_map T.continuous.measurable.aemeasurable
      (by fun_prop), charFun_apply]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    rw [T.adjoint_inner_right]
  rw [hchar, charFun_stdGaussian, charFun_stdGaussian, coisometry_adjoint_norm_sq T hT]

theorem coisometry_coordinates_hasLaw {p q : ℕ}
    (T : GaussianEuclid p →L[ℝ] GaussianEuclid q)
    (hT : T.comp T.adjoint = ContinuousLinearMap.id ℝ (GaussianEuclid q)) :
    HasLaw (fun x : Fin p → ℝ => WithLp.ofLp (T (WithLp.toLp 2 x)))
      (Measure.pi (fun _ : Fin q => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin p => gaussianReal 0 1)) := by
  have hmap : HasLaw T (stdGaussian (GaussianEuclid q)) (stdGaussian (GaussianEuclid p)) :=
    ⟨T.continuous.measurable.aemeasurable, stdGaussian_map_coisometry T hT⟩
  exact (gaussianEuclid_coordinates_hasLaw q).comp (hmap.comp (gaussianEuclid_hasLaw p))

theorem projected_normSq_inverse_integral {p q : ℕ} (hq : 2 < q)
    (T : GaussianEuclid p →L[ℝ] GaussianEuclid q)
    (hT : T.comp T.adjoint = ContinuousLinearMap.id ℝ (GaussianEuclid q)) :
    (∫ x : Fin p → ℝ, (normSq (WithLp.ofLp (T (WithLp.toLp 2 x))))⁻¹
      ∂Measure.pi (fun _ : Fin p => gaussianReal 0 1)) = 1 / ((q : ℝ) - 2) :=
  normSq_inverse_integral_of_hasLaw _ q hq _ (coisometry_coordinates_hasLaw T hT)

#assert_trust kernel stdGaussian_map_coisometry
#assert_trust kernel coisometry_coordinates_hasLaw
#assert_trust kernel projected_normSq_inverse_integral
#print axioms projected_normSq_inverse_integral
end NLA.Proofs.RE06.GaussianMoment
