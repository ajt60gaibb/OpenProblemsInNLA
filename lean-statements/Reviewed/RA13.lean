/- Frozen statement boundary. Changes reopen independent review. -/
import NLA.Statements.GaussianTrace
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! RA-13: both original absolute-error comparisons, including signed spectra.
See docs/lean/statements/RA-13/NUMERICAL_TARGETS.md.
This defines the full proposition and does not assert its truth. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Statements.GaussianTrace

namespace NLA.ReviewedStatements.RA13

noncomputable def StableRank {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (FrobeniusNorm A) ^ 2 / (SpectralNorm A) ^ 2

/-- The floor/square-root extremizer retains its final zero coordinate when
ρ is integral; its dimension is independent of the input matrix dimension. -/
noncomputable def Extremizer (lam ρ : ℝ) :
    Matrix (Fin (Nat.floor ρ + 1)) (Fin (Nat.floor ρ + 1)) ℝ :=
  fun i j => if i = j then
    if i.val < Nat.floor ρ then lam else lam * Real.sqrt (ρ - (Nat.floor ρ : ℝ))
    else 0

/-- The exact displayed threshold, with no replacement by the inconsistent
asymptotic prose in the historical source. -/
noncomputable def Threshold {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) : ℝ :=
  2 * SpectralNorm A / (m : ℝ) +
    Real.sqrt (2 * (FrobeniusNorm A) ^ 2 / (m : ℝ) +
      (2 * SpectralNorm A / (m : ℝ)) ^ 2)

/-- The first event is two-sided, the next two are upper tails.
Both upper tails are multiplied by exactly two in ℝ≥0∞, without capping. -/
noncomputable def Comparison {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (m : ℕ) (ε : ℝ) : Prop :=
  let lam := SpectralNorm A
  let φ := FrobeniusNorm A
  let ρ := StableRank A
  let B := Extremizer lam ρ
  let first := GaussianLaw m n
    {z | ε ≤ |Estimator m A z - Trace A|}
  let middle := 2 * GaussianLaw m (Nat.floor ρ + 1)
    {z | ε ≤ Estimator m B z - Trace B}
  let last := 2 * GammaLaw ((m : ℝ) * ρ / 2) ((m : ℝ) / (2 * lam))
    {x | ε ≤ x - φ ^ 2 / lam}
  first ≤ middle ∧ middle ≤ last

/-- All real nonzero symmetric inputs, including indefinite and zero-trace
matrices, with weak threshold and event inequalities. -/
def Target : Prop :=
  ∀ n : ℕ, 0 < n → ∀ A : Matrix (Fin n) (Fin n) ℝ,
    A ≠ 0 → Symmetric A → ∀ m : ℕ, 0 < m → ∀ ε : ℝ,
      Threshold A m ≤ ε → Comparison A m ε

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.RA13
