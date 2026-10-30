import NLA.Proofs.RE06.GaussianStream

/-! The finite-union and selection step of the warm start. Candidate scores
may be dependent; each bad-event bound is used only under the original law. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

/-- The exact finite-union selection inequality, independent of candidate-score
independence. The hypotheses are the individual actual-law tail bounds. -/
theorem warmStart_failure_bound_from_tails {β : Type*} [Fintype β]
    (score : β → (ℕ → ℝ) → ℝ) (tail : β → ℝ)
    (chosen : (ℕ → ℝ) → β) (optimal : β)
    (hmin : ∀ ω, score (chosen ω) ω ≤ score optimal ω)
    (s η W δlower δupper : ℝ) (hs : 0 < s) (hη : η < 1)
    (hlower : ∀ b, GaussianLaw.real {ω | score b ω < s * (1 - η) * tail b} ≤ δlower)
    (hupper : GaussianLaw.real {ω | s * (1 + η) * W < score optimal ω} ≤ δupper) :
    GaussianLaw.real {ω | ((1 + η) / (1 - η)) * W < tail (chosen ω)} ≤
      (Fintype.card β : ℝ) * δlower + δupper := by
  let badLower (b : β) : Set (ℕ → ℝ) := {ω | score b ω < s * (1 - η) * tail b}
  let badUpper : Set (ℕ → ℝ) := {ω | s * (1 + η) * W < score optimal ω}
  have hsubset : {ω | ((1 + η) / (1 - η)) * W < tail (chosen ω)} ⊆
      (⋃ b, badLower b) ∪ badUpper := by
    intro ω hbad
    by_cases hl : score (chosen ω) ω < s * (1 - η) * tail (chosen ω)
    · exact Or.inl (Set.mem_iUnion.mpr ⟨chosen ω, hl⟩)
    · right
      by_contra hu
      have hlow : s * (1 - η) * tail (chosen ω) ≤ score (chosen ω) ω := le_of_not_gt hl
      have hup : score optimal ω ≤ s * (1 + η) * W := le_of_not_gt hu
      have hscaled : s * ((1 - η) * tail (chosen ω)) ≤ s * ((1 + η) * W) := by
        nlinarith [hmin ω]
      have htail0 : (1 - η) * tail (chosen ω) ≤ (1 + η) * W :=
        le_of_mul_le_mul_left hscaled hs
      have htail : tail (chosen ω) ≤ ((1 + η) / (1 - η)) * W := by
        calc
          _ ≤ ((1 + η) * W) / (1 - η) := by
            apply (le_div_iff₀ (sub_pos.mpr hη)).2
            nlinarith
          _ = _ := by ring
      exact (not_le_of_gt hbad) htail
  calc
    _ ≤ GaussianLaw.real ((⋃ b, badLower b) ∪ badUpper) := measureReal_mono hsubset
    _ ≤ GaussianLaw.real (⋃ b, badLower b) + GaussianLaw.real badUpper :=
      measureReal_union_le _ _
    _ ≤ (∑ b, GaussianLaw.real (badLower b)) + GaussianLaw.real badUpper :=
      add_le_add (measureReal_iUnion_fintype_le (μ := GaussianLaw) badLower) le_rfl
    _ ≤ (∑ _b : β, δlower) + δupper :=
      add_le_add (Finset.sum_le_sum (fun b _ => hlower b)) hupper
    _ = _ := by simp

#assert_trust kernel warmStart_failure_bound_from_tails
#print axioms warmStart_failure_bound_from_tails
end NLA.Proofs.RE06
