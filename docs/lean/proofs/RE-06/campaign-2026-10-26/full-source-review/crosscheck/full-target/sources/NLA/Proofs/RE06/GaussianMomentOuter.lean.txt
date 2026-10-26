import NLA.Proofs.RE06.GaussianMomentOuterFoundation
import NLA.Proofs.RE06.GaussianActualRegression
import NLA.Proofs.RE06.GaussianRangeFinderMoment

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory

namespace NLA.Proofs.RE06.GaussianMoment
open NLA.Computation.NonadaptiveMatrixQuery
open Repair

theorem regression_ratio_mono {d k ell : ℕ} (hdk : d ≤ k) (hkell : k + 1 < ell) :
    0 ≤ (d : ℝ) / ((ell : ℝ) - (d : ℝ) - 1) ∧
      (d : ℝ) / ((ell : ℝ) - (d : ℝ) - 1) ≤
        (k : ℝ) / ((ell : ℝ) - (k : ℝ) - 1) := by
  have hdkR : (d : ℝ) ≤ (k : ℝ) := by exact_mod_cast hdk
  have hkellR : (k : ℝ) + 1 < (ell : ℝ) := by exact_mod_cast hkell
  have hdenD : 0 < (ell : ℝ) - (d : ℝ) - 1 := by linarith
  have hdenK : 0 < (ell : ℝ) - (k : ℝ) - 1 := by linarith
  refine ⟨div_nonneg (Nat.cast_nonneg _) hdenD.le, ?_⟩
  apply (div_le_div_iff₀ hdenD hdenK).mpr
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hprod := mul_nonneg (sub_nonneg.mpr hdkR)
    (show 0 ≤ (ell : ℝ) - 1 by linarith)
  nlinarith

theorem actual_excess_majorant_moment {n k ell : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (hr : r ≤ n)
    (hk : r + 1 < k) (hell : k + 1 < ell) :
    Integrable (fun x : RepairEntries n k ell => actualExcessMajorant C r hr
      (Matrix.of (fun i j => x.1 (i,j))) (Matrix.of (fun i j => x.2 (i,j))).transpose)
      (gaussianRepairLaw n k ell) ∧
    (∫ x : RepairEntries n k ell, actualExcessMajorant C r hr
      (Matrix.of (fun i j => x.1 (i,j))) (Matrix.of (fun i j => x.2 (i,j))).transpose
      ∂gaussianRepairLaw n k ell) ≤
        ((r : ℝ) / ((k : ℝ) - (r : ℝ) - 1) +
          (k : ℝ) / ((ell : ℝ) - (k : ℝ) - 1) +
          ((r : ℝ) / ((k : ℝ) - (r : ℝ) - 1)) *
            ((k : ℝ) / ((ell : ℝ) - (k : ℝ) - 1))) * residualTailEnergy C r := by
  let μ := Measure.pi (fun _ : Fin n × Fin k => gaussianReal 0 1)
  let ν := Measure.pi (fun _ : Fin n × Fin ell => gaussianReal 0 1)
  let G : (Fin n × Fin k → ℝ) → Matrix (Fin n) (Fin k) ℝ :=
    fun g => Matrix.of (fun i j => g (i,j))
  let Ht : (Fin n × Fin ell → ℝ) → Matrix (Fin ell) (Fin n) ℝ :=
    fun h => (Matrix.of (fun i j => h (i,j))).transpose
  let X : (Fin n × Fin k → ℝ) → ℝ := fun g => tailRandomEnergy C r hr (G g)
  let V : RepairEntries n k ell → ℝ :=
    fun x => actualRegressionEnergy (C * G x.1) C (Ht x.2)
  let a : ℝ := (r : ℝ) / ((k : ℝ) - (r : ℝ) - 1)
  let b : ℝ := (k : ℝ) / ((ell : ℝ) - (k : ℝ) - 1)
  have hrot := hasLaw_fixed_gaussian_rotation μ (exactSVD C).V (Pseudo.svd_V_cogram C) k
    id HasLaw.id
  have hX := hasLaw_rangefinder_tail_moment μ C r hr hk G hrot
  have hhead := hasLaw_rangefinder_head_right_inverse_ae μ C r hr (by omega) G hrot
  have hb : 0 ≤ b := (regression_ratio_mono (d := k) le_rfl hell).1
  have hGa : Measurable (fun x : RepairEntries n k ell => G x.1) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact (measurable_pi_apply (i,j)).comp measurable_fst
  have hHa : Measurable (fun x : RepairEntries n k ell => Ht x.2) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact (measurable_pi_apply (j,i)).comp measurable_snd
  have hVm : Measurable V := measurable_actualRegressionEnergy
    (Pseudo.measurable_matrix_mul measurable_const hGa) hHa C
  have hV0 : ∀ x, 0 ≤ V x := fun _ => actualRegressionEnergy_nonneg _ _ _
  have hinner (g : Fin n × Fin k → ℝ) := actual_regression_moment ν (C * G g) C
    (by have hdim := rangeDimension_le (C * G g); omega) id HasLaw.id
  have hVi : ∀ᵐ g ∂μ, Integrable (fun h => V (g,h)) ν :=
    Filter.Eventually.of_forall (fun g => (hinner g).1)
  have hVb : ∀ᵐ g ∂μ, (∫ h, V (g,h) ∂ν) ≤ b * (residualTailEnergy C r + X g) := by
    filter_upwards [hhead] with g hg
    change (∫ h, actualRegressionEnergy (C * G g) C (Ht h) ∂ν) ≤ _
    have hm : (∫ h, actualRegressionEnergy (C * G g) C (Ht h) ∂ν) =
        ((rangeDimension (C * G g) : ℝ) / ((ell : ℝ) - (rangeDimension (C * G g) : ℝ) - 1)) *
          squaredFrobenius (actualRangeResidual (C * G g) C) 0 := by
      simpa only [Ht, id_eq] using (hinner g).2
    rw [hm]
    calc
      _ ≤ b * squaredFrobenius (actualRangeResidual (C * G g) C) 0 :=
        mul_le_mul_of_nonneg_right
          (regression_ratio_mono (rangeDimension_le (C * G g)) hell).2
          (squaredFrobenius_zero_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (actual_rangefinder_majorant C r hr (G g) hg) hb
  have hXa : (∫ g, X g ∂μ) ≤ a * residualTailEnergy C r := by
    rw [hX.2]
    exact le_of_eq (mul_comm _ _)
  have hout := excess_prod_integrable_and_integral_le μ ν X hX.1 V hVm hV0
    a b (residualTailEnergy C r) hb hXa hVi hVb
  exact hout

theorem gaussianRepair_head_right_inverse_ae {n k ell : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (hr : r ≤ n) (hrk : r ≤ k) :
    ∀ᵐ x : RepairEntries n k ell ∂gaussianRepairLaw n k ell,
      headCoordinates C r hr (Matrix.of (fun i j => x.1 (i,j))) *
        pseudoInverse (headCoordinates C r hr (Matrix.of (fun i j => x.1 (i,j)))) = 1 := by
  have hflat : HasLaw (fun x : RepairEntries n k ell => x.1)
      (Measure.pi (fun _ : Fin n × Fin k => gaussianReal 0 1)) (gaussianRepairLaw n k ell) :=
    (measurePreserving_fst (μ := Measure.pi (fun _ : Fin n × Fin k => gaussianReal 0 1))
      (ν := Measure.pi (fun _ : Fin n × Fin ell => gaussianReal 0 1))).hasLaw
  have hrot := hasLaw_fixed_gaussian_rotation (gaussianRepairLaw n k ell) (exactSVD C).V
    (Pseudo.svd_V_cogram C) k (fun x : RepairEntries n k ell => x.1) hflat
  exact hasLaw_rangefinder_head_right_inverse_ae (gaussianRepairLaw n k ell) C r hr hrk
    (fun x => Matrix.of (fun i j => x.1 (i,j))) hrot

theorem gaussianRepair_majorant_ae {n k ell : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (hr : r ≤ n) (hrk : r ≤ k) :
    ∀ᵐ x : RepairEntries n k ell ∂gaussianRepairLaw n k ell,
      squaredFrobenius (repairErrorFromEntries C k ell x) 0 ≤
        residualTailEnergy C r + actualExcessMajorant C r hr
          (Matrix.of (fun i j => x.1 (i,j))) (Matrix.of (fun i j => x.2 (i,j))).transpose := by
  filter_upwards [gaussianRepair_head_right_inverse_ae (ell := ell) C r hr hrk] with x hx
  exact actual_svd_repair_majorant C r hr _ _ hx

end NLA.Proofs.RE06.GaussianMoment
