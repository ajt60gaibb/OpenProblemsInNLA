import NLA.PF03.NoRationalFactor
import NLA.PF03.RationalConeHalfspaces
import NLA.PF03.CPBoundary

/-! C24/C25: unconditional negation of the unchanged canonical question.
The rational halfspace representation is constructed by the proved finite
projection theorem; all internal cone and kernel hypotheses are discharged.
Sidney Holden: original mathematics. George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology: formalization;
Codex assistance. Author: /root. -/
set_option autoImplicit false
open scoped BigOperators Classical Matrix
noncomputable section
namespace NLA.PF03

theorem pf03_counterexample :
    ∃ n : ℕ, 5 ≤ n ∧ ∃ A : SymMatrix ℚ n,
      realCast A ∈ frontier (CPSet n) ∧ ¬ RationalFactor A := by
  obtain ⟨N, R, hrep⟩ := rational_cone_halfspaces generatorMatrix
  have hR : HSet R = K := Set.ext (fun x => (hrep x).symm)
  obtain ⟨hN, hdiag, hnonneg, hgram, hpad, hkernel⟩ := padded_real_factor R hR
  refine ⟨N + 5, hN, paddedGram R, ?_, ?_⟩
  · apply cp_zero_diagonal_frontier (by omega) (realCast (paddedGram R))
      ⟨7, by decide, paddedRealFactor R, hnonneg, hgram⟩ (paddedIndex N)
    change ((paddedGram R).val (paddedIndex N) (paddedIndex N) : ℝ) = 0
    rw [hdiag, Rat.cast_zero]
  · rintro ⟨m, hm, C, hCpos, hC⟩
    have hp : NoLine (HSet (padRows R)) := by rw [hpad]; exact K_noLine
    exact no_rational_factor (padRows R) hpad
      (pointed_halfspaces_injective (padRows R) hp).1 m hm C hCpos hC.symm

theorem canonical_negative_answer : ¬ RationalBoundaryFactorability := by
  intro h
  obtain ⟨n, hn, A, hboundary, hno⟩ := pf03_counterexample
  exact hno (h n hn A hboundary)

#print axioms pf03_counterexample
#assert_trust kernel pf03_counterexample
#print axioms canonical_negative_answer
#assert_trust kernel canonical_negative_answer
end NLA.PF03
