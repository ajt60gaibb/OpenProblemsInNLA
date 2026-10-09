import NLA.Statements.RowDeletion
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! IE-21: original spherical row-deletion limit, separately retained from
Colbrook's supplied quantitative answer. The combined statement checks both.
See docs/lean/statements/IE-21/NUMERICAL_TARGETS.md; neither target is proved. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Filter
open NLA.Statements.RowDeletion

namespace NLA.Statements.IE21

/-- The exact original displayed limit, with both growth assumptions. -/
def OriginalLimitTarget : Prop :=
  ∀ θ a : ℝ, 0 < θ → θ < 1 → 0 < a → GaussianQuantile θ a →
    ∀ m n : ℕ → ℕ, (∀ j, 0 < m j) → (∀ j, 0 < n j) →
      Tendsto (fun j => (n j : ℝ)) atTop atTop →
      Tendsto (fun j => (m j : ℝ) / (n j : ℝ)) atTop atTop →
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun j => MatrixLaw (m j) (n j) {ω |
          ε ≤ |SubsingularSquared θ (SampleMatrix ω) /
            OperatorSquared (SampleMatrix ω) - TrimmedMoment a|})
          atTop (nhds 0)

/-- A credited stronger, explicit answer to the source's unprescribed
quantitative request. Both error inequalities hold outside one common event. -/
def QuantitativeAnswerTarget : Prop :=
  ∀ θ a : ℝ, 0 < θ → θ < 1 → 0 < a → GaussianQuantile θ a →
    ∀ m n : ℕ, 1 ≤ m → 2 ≤ n →
      ∀ t δ η : ℝ, 0 < t → t < 1 → 0 < δ → δ < 1 →
        0 < η → η ≤ (1 - θ) / 2 →
        let L := 2 / (1 - θ)
        let D := 2 * L * η + L / (m : ℝ) + 2 * (1 + t) * δ
        let E := D + Real.sqrt (2 / (n : ℝ))
        let F := (E + t) / (1 - t)
        let B := 2 * (9 : ℝ) ^ n * Real.exp (-(m : ℝ) * t ^ 2 / 512) +
          5 * (1 + 2 / δ) ^ n * Real.exp (-2 * (m : ℝ) * η ^ 2)
        MatrixLaw m n {ω |
          E < |((n : ℝ) / (m : ℝ)) * SubsingularSquared θ (SampleMatrix ω) -
            TrimmedMoment a| ∨
          F < |SubsingularSquared θ (SampleMatrix ω) /
            OperatorSquared (SampleMatrix ω) - TrimmedMoment a|} ≤ ENNReal.ofReal B

def Target : Prop := OriginalLimitTarget ∧ QuantitativeAnswerTarget

#assert_statement OriginalLimitTarget
#assert_statement QuantitativeAnswerTarget
#assert_statement Target
#assert_trust kernel OriginalLimitTarget
#assert_trust kernel QuantitativeAnswerTarget
#assert_trust kernel Target
#print axioms Target

end NLA.Statements.IE21
