import NLA.TR13.Definitions

/-! The full TR-13 statement compares every width-at-most predicate, not only
the five infimum ranks. This proposition is shared by the proof bridge and the
independent challenge boundary. -/

set_option autoImplicit false

namespace NLA.TR13

/-- Exact all-width target on one tensor: ordinary width is equivalent to
symmetric, ordinary-border, symmetric-border, and Vandermonde width at each
natural width, including zero. -/
def EqualFiveWidths {m n : ℕ} (T : Tensor m n) : Prop :=
  ∀ q : ℕ,
    (OrdinaryRankAtMost q T ↔ SymmetricRankAtMost q T) ∧
    (OrdinaryRankAtMost q T ↔ OrdinaryBorderRankAtMost q T) ∧
    (OrdinaryRankAtMost q T ↔ SymmetricBorderRankAtMost q T) ∧
    (OrdinaryRankAtMost q T ↔ VandermondeRankAtMost q T)

end NLA.TR13
