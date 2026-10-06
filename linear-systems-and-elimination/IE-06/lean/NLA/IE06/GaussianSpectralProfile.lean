import NLA.IE06.SelectedBlockExtension

/-! Unconditional simultaneous selected-block retained-inverse bound. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
namespace NLA.IE06.GaussianSpectralProfile
open GaussianNull SelectedBlockExtensionScalars GaussianSpectralRecursion

/-- A uniform loss constant sufficient for both the Gaussian base case and the
proved selected-block extension at every recursion step. -/
def profileConstant (β : ℝ) : ℝ := max (100*extensionConstant β) (4*β+4004)

theorem profileConstant_nonneg {β : ℝ} (hβ : 1 ≤ β) : 0 ≤ profileConstant β := by
  exact (by linarith : (0:ℝ) ≤ 4*β+4004).trans (le_max_right _ _)

/-- Uniformly in every selected prefix and every retained cutoff above
`ceil(sqrt(log n))`, the inverse-square sum has the stated Gaussian tail.
All manuscript probability inputs have been proved and supplied here. -/
theorem inverse_tail {β : ℝ} (hβ : 1 ≤ β) {n : ℕ} (hlog : 256 ≤ Real.log (n:ℝ)) :
    gaussianMatrix n (inverseBad n ⌈Real.sqrt (Real.log (n:ℝ))⌉₊ (profileConstant β)) ≤
      ENNReal.ofReal (Real.exp (-(β-2)*Real.log (n:ℝ))) := by
  exact inverse_tail_of_extension_bound hlog hβ (extensionConstant_pos hβ).le
    (le_max_right _ _) (le_max_left _ _) (SelectedBlockExtension.extension_bound n hβ)

theorem exists_inverse_tail {β : ℝ} (hβ : 1 ≤ β) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 256 ≤ Real.log (n:ℝ) →
      gaussianMatrix n (inverseBad n ⌈Real.sqrt (Real.log (n:ℝ))⌉₊ D) ≤
        ENNReal.ofReal (Real.exp (-(β-2)*Real.log (n:ℝ))) :=
  ⟨profileConstant β,profileConstant_nonneg hβ,fun _ hlog => inverse_tail hβ hlog⟩

#assert_trust kernel profileConstant
#print axioms profileConstant
#assert_trust kernel profileConstant_nonneg
#print axioms profileConstant_nonneg
#assert_trust kernel inverse_tail
#print axioms inverse_tail
#assert_trust kernel exists_inverse_tail
#print axioms exists_inverse_tail

end NLA.IE06.GaussianSpectralProfile
