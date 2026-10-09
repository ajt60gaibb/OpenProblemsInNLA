import NLA.Statements.GaussianTrace
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! RA-12: both original relative-error Gaussian trace comparisons.
See docs/lean/statements/RA-12/NUMERICAL_TARGETS.md.
This defines the full proposition and does not assert its truth. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Statements.GaussianTrace

namespace NLA.Statements.RA12

noncomputable def EffectiveRank {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Trace A / SpectralNorm A

/-- Dimension `floor μ + 1` retains the final zero coordinate when μ is integral.
In the target μ≥1 follows from nonzero real PSD input; it is not an extra premise. -/
noncomputable def Extremizer (μ : ℝ) :
    Matrix (Fin (Nat.floor μ + 1)) (Fin (Nat.floor μ + 1)) ℝ :=
  fun i j => if i = j then
    if i.val < Nat.floor μ then 1 / μ else (μ - (Nat.floor μ : ℝ)) / μ
    else 0

/-- The actual complete probability chain, with both weak comparisons. -/
noncomputable def Comparison {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (m : ℕ) (ε : ℝ) : Prop :=
  let μ := EffectiveRank A
  let B := Extremizer μ
  let first := GaussianLaw m n
    {z | ε * Trace A ≤ |Estimator m A z - Trace A|}
  let middle := GaussianLaw m (Nat.floor μ + 1)
    {z | ε ≤ |Estimator m B z - 1|}
  let last := GammaLaw ((m : ℝ) * μ / 2) ((m : ℝ) * μ / 2)
    {x | ε ≤ |x - 1|}
  first ≤ middle ∧ middle ≤ last

/-- All nonzero PSD inputs and all positive sample counts are retained,
including equality at the exact relative-error threshold. -/
def Target : Prop :=
  ∀ n : ℕ, 0 < n → ∀ A : Matrix (Fin n) (Fin n) ℝ,
    A ≠ 0 → Symmetric A → NonnegativeQuadraticForm A →
    ∀ m : ℕ, 0 < m → ∀ ε : ℝ,
      2 / ((m : ℝ) * EffectiveRank A) ≤ ε → Comparison A m ε

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.Statements.RA12
