import ProofProject.SourcePolynomialHilbert
import ProofProject.SourceDirichletGain

/-! The explicit alternating gain in the actual normalized Hilbert family. -/

noncomputable section

namespace ProofProject

lemma sourcePolynomial_one (n : ℕ) (θ : ℝ) :
    sourcePolynomial (fun _ : Fin n => (1 : ℂ)) θ = dirichletKernel n θ := by
  simp only [sourcePolynomial, one_mul, dirichletKernel_eq_sum_fin, sourceCircle]

/-- The actual unit Hilbert family realizes the sharp explicit sign gain.
Only its uniform adjacent-tail boundary estimate remains to construct the
boundary models; no norm attainment or additional analytic gain premise is used. -/
theorem sourceUnitFamily_alternating_gain {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℕ, 1 ≤ n →
      (d * (n : ℝ) ^ α) ^ 2 *
        ‖finiteSynthesis (sourceUnitFamily α hα0 hα1)
          (fun i : Fin n => (-1 : ℂ) ^ i.val)‖ ^ 2 ≤
        ‖finiteSynthesis (sourceUnitFamily α hα0 hα1) (fun _ : Fin n => (1 : ℂ))‖ ^ 2 := by
  obtain ⟨d, hd, hgain⟩ := source_dirichlet_alternating_gain_set hα0 hα1
  refine ⟨d, hd, ?_⟩
  intro n hn
  rw [sourceUnitFamily_synthesis_norm_sq, sourceUnitFamily_synthesis_norm_sq]
  simp only [sourcePolynomial_one]
  have h := mul_le_mul_of_nonneg_left (hgain n hn) (inv_nonneg.mpr (sourceWeightMass_nonneg α))
  simpa only [sourcePolynomial, mul_left_comm, mul_assoc] using h

end ProofProject
