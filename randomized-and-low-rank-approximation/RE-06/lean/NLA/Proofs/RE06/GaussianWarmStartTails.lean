import NLA.Proofs.RE06.GaussianTailTransport
import NLA.Proofs.RE06.GaussianWarmStart

/-! Uniform warm-start trimmed-tail control under the original stream law.
Each candidate's rotated coordinates have a proved product law; the scores
for different candidates need not be independent. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

/-- Source-strength finite-family warm-start bound from actual coordinate laws. -/
theorem gaussian_warmStart_tail_bound (s : ℕ) (hs : 0 < s)
    (X : β → (ℕ → ℝ) → (ι × Fin s → ℝ))
    (hX : ∀ b, HasLaw (X b) (Measure.pi (fun _ : ι × Fin s => gaussianReal 0 1)) GaussianLaw)
    (w : β → ι → ℝ) (hw : ∀ b i, 0 ≤ w b i) (head : Finset ι)
    (a : β → ℝ) (ha : ∀ b, 0 ≤ a b)
    (hhead : ∀ b i, i ∈ head → a b ≤ w b i)
    (htail : ∀ b i, i ∉ head → w b i ≤ a b)
    (chosen : (ℕ → ℝ) → β) (optimal : β)
    (hmin : ∀ ω,
      gaussianQuadratic (fun p : ι × Fin s => w (chosen ω) p.1) (X (chosen ω) ω) ≤
      gaussianQuadratic (fun p : ι × Fin s => w optimal p.1) (X optimal ω))
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    GaussianLaw.real {ω | ((1 + η) / (1 - η)) * (∑ i, w optimal i) <
      ∑ i ∈ headᶜ, w (chosen ω) i} ≤
      (Fintype.card β : ℝ) * Real.exp (-(s : ℝ) * (head.card : ℝ) * η / 4) +
        Real.exp (-(s : ℝ) * η ^ 2 / 8) := by
  exact warmStart_failure_bound_from_tails
    (fun b ω => gaussianQuadratic (fun p : ι × Fin s => w b p.1) (X b ω))
    (fun b => ∑ i ∈ headᶜ, w b i) chosen optimal hmin (s : ℝ) η
    (∑ i, w optimal i) (Real.exp (-(s : ℝ) * (head.card : ℝ) * η / 4))
    (Real.exp (-(s : ℝ) * η ^ 2 / 8)) (Nat.cast_pos.mpr hs) hη1
    (fun b => gaussianQuadratic_trimmed_lower_tail_of_hasLaw s (X b) (hX b)
      (w b) (hw b) head (a b) (ha b) (hhead b) (htail b) η hη0 hη1.le)
    (gaussianQuadratic_upper_tail_of_hasLaw s (X optimal) (hX optimal)
      (w optimal) (hw optimal) η hη0 hη1.le)

#assert_trust kernel gaussian_warmStart_tail_bound
#print axioms gaussian_warmStart_tail_bound
end NLA.Proofs.RE06
