import NLA.Proofs.RE06.GaussianMomentFubini
import NLA.Proofs.RE06.PseudoInverseGlobalMeasurable

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace NLA.Proofs.RE06.GaussianMoment
open NLA.Computation.NonadaptiveMatrixQuery

def gramInverseEntry {d p : ℕ} (i : Fin d) (x : (Fin d × Fin p) → ℝ) : ℝ :=
  (entryMatrix x * (entryMatrix x).transpose)⁻¹ i i

theorem entryMatrix_measurable (d p : ℕ) :
    Measurable (entryMatrix (d := d) (p := p)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact measurable_pi_apply (i,j)

theorem gramInverseEntry_measurable {d p : ℕ} (i : Fin d) :
    Measurable (gramInverseEntry (p := p) i) := by
  have hm := entryMatrix_measurable d p
  have hG := Pseudo.measurable_matrix_mul hm (Pseudo.measurable_matrix_transpose hm)
  have hi := (Pseudo.measurable_nonsing_inverse d).comp hG
  exact (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hi)

theorem gramInverseEntry_zero_integrable (d p : ℕ) (hdp : d + 2 < p) :
    Integrable (gramInverseEntry (p := p) (0 : Fin (d + 1)))
      (Measure.pi (fun _ : Fin (d + 1) × Fin p => gaussianReal 0 1)) := by
  have hlaw := joinedEntries_hasLaw d p
  have hh := integrable_map_measure
    (f := joinedEntries (d := d) (p := p))
    (μ := (Measure.pi (fun _ : Fin d × Fin p => gaussianReal 0 1)).prod
      (Measure.pi (fun _ : Fin p => gaussianReal 0 1)))
    (g := gramInverseEntry (p := p) (0 : Fin (d + 1)))
    (gramInverseEntry_measurable _).aestronglyMeasurable
    hlaw.aemeasurable
  rw [hlaw.map_eq] at hh
  exact hh.mpr (joinedGramEntry_integrable d p hdp)

theorem gramInverseEntry_zero_integral (d p : ℕ) (hdp : d + 2 < p) :
    (∫ x, gramInverseEntry (p := p) (0 : Fin (d + 1)) x
      ∂Measure.pi (fun _ : Fin (d + 1) × Fin p => gaussianReal 0 1)) =
        1 / ((p : ℝ) - (d : ℝ) - 2) := by
  have hlaw := joinedEntries_hasLaw d p
  have hh := hlaw.integral_comp
    (gramInverseEntry_zero_integrable d p hdp).aestronglyMeasurable
  exact hh.symm.trans (joinedGramEntry_integral d p hdp)

def permutedEntries {d p : ℕ} (e : Fin d ≃ Fin d) (x : (Fin d × Fin p) → ℝ) :
    (Fin d × Fin p) → ℝ := fun ij => x (e ij.1, ij.2)

theorem permutedEntries_hasLaw {d p : ℕ} (e : Fin d ≃ Fin d) :
    HasLaw (permutedEntries (p := p) e)
      (Measure.pi (fun _ : Fin d × Fin p => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin d × Fin p => gaussianReal 0 1)) := by
  have hh := (measurePreserving_piCongrLeft
    (fun _ : Fin d × Fin p => gaussianReal 0 1)
    (e.symm.prodCongr (Equiv.refl (Fin p)))).hasLaw
  convert hh using 1
  funext x ij
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, permutedEntries]

theorem gramInverseEntry_permuted {d p : ℕ} (e : Fin d ≃ Fin d) (i : Fin d)
    (x : (Fin d × Fin p) → ℝ) :
    gramInverseEntry i (permutedEntries e x) = gramInverseEntry (e i) x := by
  have hM : entryMatrix (permutedEntries e x) = (entryMatrix x).submatrix e id := rfl
  have hG : entryMatrix (permutedEntries e x) * (entryMatrix (permutedEntries e x)).transpose =
      (entryMatrix x * (entryMatrix x).transpose).submatrix e e := by
    rw [hM, Matrix.transpose_submatrix]
    exact Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl (Fin p)) _
  unfold gramInverseEntry
  rw [hG, Matrix.inv_submatrix_equiv]
  rfl

theorem gramInverseEntry_integrable (d p : ℕ) (hdp : d + 2 < p) (i : Fin (d + 1)) :
    Integrable (gramInverseEntry (p := p) i)
      (Measure.pi (fun _ : Fin (d + 1) × Fin p => gaussianReal 0 1)) := by
  let e := Equiv.swap (0 : Fin (d + 1)) i
  have hlaw := permutedEntries_hasLaw (p := p) e
  have hi := gramInverseEntry_zero_integrable d p hdp
  have himap : Integrable (gramInverseEntry (p := p) (0 : Fin (d + 1)))
      ((Measure.pi (fun _ : Fin (d + 1) × Fin p => gaussianReal 0 1)).map
        (permutedEntries (p := p) e)) := by rw [hlaw.map_eq]; exact hi
  have hc := himap.comp_aemeasurable hlaw.aemeasurable
  simpa only [Function.comp_def, gramInverseEntry_permuted, e, Equiv.swap_apply_left] using hc

theorem gramInverseEntry_integral (d p : ℕ) (hdp : d + 2 < p) (i : Fin (d + 1)) :
    (∫ x, gramInverseEntry (p := p) i x
      ∂Measure.pi (fun _ : Fin (d + 1) × Fin p => gaussianReal 0 1)) =
        1 / ((p : ℝ) - (d : ℝ) - 2) := by
  let e := Equiv.swap (0 : Fin (d + 1)) i
  have hlaw := permutedEntries_hasLaw (p := p) e
  have hh := hlaw.integral_comp
    (gramInverseEntry_zero_integrable d p hdp).aestronglyMeasurable
  simp only [Function.comp_def, gramInverseEntry_permuted, e, Equiv.swap_apply_left] at hh
  exact hh.trans (gramInverseEntry_zero_integral d p hdp)

theorem trace_inverse_gram_integrable (d p : ℕ) (hdp : d + 2 < p) :
    Integrable (fun x : (Fin (d + 1) × Fin p) → ℝ =>
      Matrix.trace (entryMatrix x * (entryMatrix x).transpose)⁻¹)
      (Measure.pi (fun _ : Fin (d + 1) × Fin p => gaussianReal 0 1)) := by
  exact integrable_finsetSum Finset.univ (fun i _ => gramInverseEntry_integrable d p hdp i)

theorem trace_inverse_gram_integral (d p : ℕ) (hdp : d + 2 < p) :
    (∫ x : (Fin (d + 1) × Fin p) → ℝ,
      Matrix.trace (entryMatrix x * (entryMatrix x).transpose)⁻¹
      ∂Measure.pi (fun _ : Fin (d + 1) × Fin p => gaussianReal 0 1)) =
        ((d : ℝ) + 1) / ((p : ℝ) - (d : ℝ) - 2) := by
  change (∫ x, ∑ i, gramInverseEntry (p := p) i x ∂_) = _
  rw [integral_finsetSum Finset.univ (fun i _ => gramInverseEntry_integrable d p hdp i)]
  simp only [gramInverseEntry_integral d p hdp, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul]

theorem pseudoinverse_frobeniusSq_integrable (d p : ℕ) (hdp : d + 1 < p) :
    Integrable (fun x : (Fin d × Fin p) → ℝ => Pseudo.frobeniusSq (pseudoInverse (entryMatrix x)))
      (Measure.pi (fun _ : Fin d × Fin p => gaussianReal 0 1)) := by
  cases d with
  | zero => simpa [Pseudo.frobeniusSq] using
      (integrable_const (0 : ℝ) : Integrable (fun _ : (Fin 0 × Fin p) → ℝ => (0 : ℝ)) _)
  | succ d =>
    have hh := trace_inverse_gram_integrable d p (by omega)
    apply hh.congr
    filter_upwards [gaussian_gram_det_ne_zero_ae (d + 1) p (by omega)] with x hx
    exact (Pseudo.full_row_frobeniusSq_trace_inverse_gram (entryMatrix x) hx).symm

theorem pseudoinverse_frobeniusSq_integral (d p : ℕ) (hdp : d + 1 < p) :
    (∫ x : (Fin d × Fin p) → ℝ, Pseudo.frobeniusSq (pseudoInverse (entryMatrix x))
      ∂Measure.pi (fun _ : Fin d × Fin p => gaussianReal 0 1)) =
        (d : ℝ) / ((p : ℝ) - (d : ℝ) - 1) := by
  cases d with
  | zero => simp [Pseudo.frobeniusSq]
  | succ d =>
    have he : (fun x : (Fin (d + 1) × Fin p) → ℝ =>
        Pseudo.frobeniusSq (pseudoInverse (entryMatrix x))) =ᵐ[
          Measure.pi (fun _ : Fin (d + 1) × Fin p => gaussianReal 0 1)]
        (fun x => Matrix.trace (entryMatrix x * (entryMatrix x).transpose)⁻¹) := by
      filter_upwards [gaussian_gram_det_ne_zero_ae (d + 1) p (by omega)] with x hx
      exact Pseudo.full_row_frobeniusSq_trace_inverse_gram (entryMatrix x) hx
    rw [integral_congr_ae he, trace_inverse_gram_integral d p (by omega)]
    push_cast
    congr 1
    ring

end NLA.Proofs.RE06.GaussianMoment
