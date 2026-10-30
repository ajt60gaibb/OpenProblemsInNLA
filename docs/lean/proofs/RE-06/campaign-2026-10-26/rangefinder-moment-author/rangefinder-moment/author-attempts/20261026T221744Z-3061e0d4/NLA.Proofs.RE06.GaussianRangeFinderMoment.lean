import NLA.Proofs.RE06.GaussianRangeFinderCoordinates
import NLA.Proofs.RE06.GaussianProductMomentTransport
import NLA.Proofs.RE06.PseudoInverseGlobalMeasurable
import NLA.Proofs.RE06.GaussianMomentInverse

/-! Actual SVD range-finder tail energy: exact expectation from independent
Gaussian head/tail rows and the proved rectangular pseudoinverse moment. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Matrix
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

theorem gaussian_pseudoinverse_energy_integrable (r k : ℕ) (hk : r + 1 < k) :
    Integrable (fun x : Fin r × Fin k → ℝ =>
      squaredFrobenius (pseudoInverse (Matrix.of (fun i j => x (i,j)))) 0)
      (Measure.pi (fun _ : Fin r × Fin k => gaussianReal 0 1)) := by
  have he (x : Fin r × Fin k → ℝ) : Matrix.of (fun i j => x (i,j)) =
      GaussianMoment.entryMatrix x := by ext i j; rfl
  simp_rw [he]
  simpa only [squaredFrobenius, Matrix.zero_apply, sub_zero, Pseudo.frobeniusSq] using
    GaussianMoment.pseudoinverse_frobeniusSq_integrable r k hk

theorem gaussian_pseudoinverse_energy_integral (r k : ℕ) (hk : r + 1 < k) :
    (∫ x : Fin r × Fin k → ℝ,
      squaredFrobenius (pseudoInverse (Matrix.of (fun i j => x (i,j)))) 0
      ∂Measure.pi (fun _ : Fin r × Fin k => gaussianReal 0 1)) =
        (r : ℝ) / ((k : ℝ) - (r : ℝ) - 1) := by
  have he (x : Fin r × Fin k → ℝ) : Matrix.of (fun i j => x (i,j)) =
      GaussianMoment.entryMatrix x := by ext i j; rfl
  simp_rw [he]
  simpa only [squaredFrobenius, Matrix.zero_apply, sub_zero, Pseudo.frobeniusSq] using
    GaussianMoment.pseudoinverse_frobeniusSq_integral r k hk

theorem measurable_gaussian_pseudoinverse_entries (r k : ℕ) (i : Fin k) (j : Fin r) :
    Measurable (fun x : Fin r × Fin k → ℝ =>
      pseudoInverse (Matrix.of (fun l z => x (l,z))) i j) := by
  have hm : Measurable (fun x : Fin r × Fin k → ℝ =>
      Matrix.of (fun l z => x (l,z))) := by
    apply measurable_pi_lambda
    intro l
    apply measurable_pi_lambda
    intro z
    exact measurable_pi_apply (l,z)
  exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
    ((Pseudo.measurable_actual r k).comp hm))

/-- Exact integrability and expectation for the split coordinates, before
transport through the fixed actual SVD rotation. -/
theorem gaussian_split_rangefinder_moment {n k : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (hr : r ≤ n) (hk : r + 1 < k) :
    Integrable (fun x : Fin n × Fin k → ℝ => squaredFrobenius
      (gaussianWeightedTail C r hr *
        Matrix.of (fun l j => gaussianTailEntries n r k hr x (l,j)) *
        pseudoInverse (Matrix.of (fun i j => gaussianHeadEntries n r k hr x (i,j)))) 0)
      (Measure.pi (fun _ : Fin n × Fin k => gaussianReal 0 1)) ∧
    (∫ x : Fin n × Fin k → ℝ, squaredFrobenius
      (gaussianWeightedTail C r hr *
        Matrix.of (fun l j => gaussianTailEntries n r k hr x (l,j)) *
        pseudoInverse (Matrix.of (fun i j => gaussianHeadEntries n r k hr x (i,j)))) 0
      ∂Measure.pi (fun _ : Fin n × Fin k => gaussianReal 0 1)) =
      residualTailEnergy C r * ((r : ℝ) / ((k : ℝ) - (r : ℝ) - 1)) := by
  let ν := Measure.pi (fun _ : Fin r × Fin k => gaussianReal 0 1)
  let U : (Fin r × Fin k → ℝ) → Matrix (Fin n) (Fin (n-r)) ℝ :=
    fun _ => gaussianWeightedTail C r hr
  let V : (Fin r × Fin k → ℝ) → Matrix (Fin k) (Fin r) ℝ :=
    fun y => pseudoInverse (Matrix.of (fun i j => y (i,j)))
  have hU : ∀ i l, Measurable (fun y => U y i l) := fun _ _ => measurable_const
  have hV : ∀ l j, Measurable (fun y => V y l j) :=
    measurable_gaussian_pseudoinverse_entries r k
  have henergy : Integrable (fun y => squaredFrobenius (U y) 0 * squaredFrobenius (V y) 0) ν := by
    dsimp only [U, V, ν]
    exact (gaussian_pseudoinverse_energy_integrable r k hk).const_mul
      (squaredFrobenius (gaussianWeightedTail C r hr) 0)
  have hi := hasLaw_gaussian_product_fubini_integrable ν U V hU hV henergy
    (gaussianHeadEntries n r k hr) (gaussianTailEntries n r k hr)
    (gaussian_row_split_hasLaw n r k hr)
  have he := hasLaw_gaussian_product_fubini_integral ν U V hU hV henergy
    (gaussianHeadEntries n r k hr) (gaussianTailEntries n r k hr)
    (gaussian_row_split_hasLaw n r k hr)
  constructor
  · exact hi
  · calc
      _ = ∫ y : Fin r × Fin k → ℝ,
          squaredFrobenius (gaussianWeightedTail C r hr) 0 *
          squaredFrobenius (pseudoInverse (Matrix.of (fun i j => y (i,j)))) 0 ∂ν := he
      _ = _ := by
        rw [integral_const_mul, gaussian_pseudoinverse_energy_integral r k hk,
          gaussianWeightedTail_energy]

theorem headCoordinates_eq_gaussian_entries {n k : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (hr : r ≤ n)
    (G : Matrix (Fin n) (Fin k) ℝ) :
    Repair.headCoordinates C r hr G = Matrix.of (fun i j =>
      gaussianHeadEntries n r k hr (fun p => ((exactSVD C).V.transpose * G) p.1 p.2) (i,j)) := by
  rw [gaussian_head_entries_matrix]
  have he : Matrix.of (fun i j => ((exactSVD C).V.transpose * G) i j) =
      (exactSVD C).V.transpose * G := by ext i j; rfl
  rw [he]
  unfold Repair.headCoordinates
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- The actual SVD head coordinates have a right inverse almost surely, with
no rank assumption imposed on the fixed residual matrix. -/
theorem hasLaw_rangefinder_head_right_inverse_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n k : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (r : ℕ) (hr : r ≤ n) (hrk : r ≤ k) (G : Ω → Matrix (Fin n) (Fin k) ℝ)
    (hG : HasLaw (fun ω (p : Fin n × Fin k) => ((exactSVD C).V.transpose * G ω) p.1 p.2)
      (Measure.pi (fun _ : Fin n × Fin k => gaussianReal 0 1)) μ) :
    ∀ᵐ ω ∂μ, Repair.headCoordinates C r hr (G ω) *
      pseudoInverse (Repair.headCoordinates C r hr (G ω)) = 1 := by
  have hlaw := (gaussian_head_entries_hasLaw n r k hr).fun_comp hG
  have hdet := GaussianMoment.hasLaw_gram_det_ne_zero_ae μ r k hrk _ hlaw
  filter_upwards [hdet] with ω hω
  rw [headCoordinates_eq_gaussian_entries]
  let M : Matrix (Fin r) (Fin k) ℝ := Matrix.of (fun i j => gaussianHeadEntries n r k hr
    (fun p => ((exactSVD C).V.transpose * G ω) p.1 p.2) (i,j))
  have hd : (M * M.transpose).det ≠ 0 := hω
  change M * pseudoInverse M = 1
  rw [Pseudo.full_row_formula M hd, ← Matrix.mul_assoc]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd)

/-- A genuine law for all rotated coordinates is sufficient; no measurable
SVD selection in the residual matrix is needed. -/
theorem hasLaw_rangefinder_tail_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n k : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (hr : r ≤ n) (hk : r + 1 < k)
    (G : Ω → Matrix (Fin n) (Fin k) ℝ)
    (hG : HasLaw (fun ω (p : Fin n × Fin k) => ((exactSVD C).V.transpose * G ω) p.1 p.2)
      (Measure.pi (fun _ : Fin n × Fin k => gaussianReal 0 1)) μ) :
    Integrable (fun ω => Repair.tailRandomEnergy C r hr (G ω)) μ ∧
    (∫ ω, Repair.tailRandomEnergy C r hr (G ω) ∂μ) =
      residualTailEnergy C r * ((r : ℝ) / ((k : ℝ) - (r : ℝ) - 1)) := by
  have hm := gaussian_split_rangefinder_moment C r hr hk
  have himap := hm.1
  rw [← hG.map_eq] at himap
  have hi := himap.comp_aemeasurable hG.aemeasurable
  have he := hG.integral_comp hm.1.aestronglyMeasurable
  constructor
  · simpa only [Function.comp_def, ← tailRandomEnergy_eq_split_product] using hi
  · simpa only [Function.comp_def, ← tailRandomEnergy_eq_split_product] using he.trans hm.2

/-- The original contiguous stream block has the required fixed-SVD rotation
law, giving the literal actual range-finder expectation. -/
theorem stream_rangefinder_tail_moment {n k : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (hr : r ≤ n) (hk : r + 1 < k) (offset : ℕ) :
    Integrable (fun ω => Repair.tailRandomEnergy C r hr (gaussianBlock n k offset ω)) GaussianLaw ∧
    (∫ ω, Repair.tailRandomEnergy C r hr (gaussianBlock n k offset ω) ∂GaussianLaw) =
      residualTailEnergy C r * ((r : ℝ) / ((k : ℝ) - (r : ℝ) - 1)) := by
  exact hasLaw_rangefinder_tail_moment GaussianLaw C r hr hk
    (gaussianBlock n k offset) (residualGaussianCoordinates_hasLaw C k offset)

#assert_trust kernel headCoordinates_eq_gaussian_entries
#assert_trust kernel hasLaw_rangefinder_head_right_inverse_ae
#print axioms headCoordinates_eq_gaussian_entries
#print axioms hasLaw_rangefinder_head_right_inverse_ae
#assert_trust kernel gaussian_pseudoinverse_energy_integrable
#assert_trust kernel gaussian_pseudoinverse_energy_integral
#assert_trust kernel measurable_gaussian_pseudoinverse_entries
#assert_trust kernel gaussian_split_rangefinder_moment
#assert_trust kernel hasLaw_rangefinder_tail_moment
#assert_trust kernel stream_rangefinder_tail_moment
#print axioms gaussian_pseudoinverse_energy_integrable
#print axioms gaussian_pseudoinverse_energy_integral
#print axioms measurable_gaussian_pseudoinverse_entries
#print axioms gaussian_split_rangefinder_moment
#print axioms hasLaw_rangefinder_tail_moment
#print axioms stream_rangefinder_tail_moment
end NLA.Proofs.RE06
