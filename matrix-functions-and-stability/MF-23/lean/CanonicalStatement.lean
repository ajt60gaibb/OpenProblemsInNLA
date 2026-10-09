import OAI.Analysis.DirectCrouzeix.Model

/-!
This is the canonical MF-23 block order from the published README. It is a
statement only. The `OAI` import is the immutable upstream Model.lean at
openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

namespace NLA.MF23

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

def blockEvaluation {n m d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  ∑ k : Fin (d + 1), (B k) ⊗ₖ (A ^ (k : ℕ))

def CanonicalUniversalBound (c : ℝ) : Prop :=
  ∀ (n m d : ℕ), 0 < n → 0 < m →
    ∀ (A : Matrix (Fin n) (Fin n) ℂ)
      (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ),
      ‖blockEvaluation A B‖ ≤ c * OAI.DirectCrouzeix.rangeMaximum A B

def Target : Prop := CanonicalUniversalBound 2

end

end NLA.MF23
