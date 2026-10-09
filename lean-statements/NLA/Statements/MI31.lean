import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Matrix.Basic
import NLA.Statements.Infrastructure
import NLA.Statements.Shared.MI31Exponent
import LeanCert.Tactic.Verification

/-! MI-31: the original universal-constant upper bound for the expected
induced ℓ_p-to-ℓ_q norm of an entrywise Gaussian real matrix. The full
source and numerical contract are retained in docs/lean/statements/MI-31/.
This is a statement definition, not a proof of the conjecture. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace NLA.Statements.MI31

/-- Finite-dimensional ℓ_r for a real exponent. This is the usual norm on
the target domain `r ≥ 1`; the definition does not round real powers. -/
noncomputable def FiniteLpNorm {n : ℕ} (r : ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.rpow (∑ i : Fin n, Real.rpow |x i| r) (1 / r)

/-- The maximum norm. Positive target dimensions make the coordinate set
nonempty, so this supremum is a genuine finite maximum. -/
noncomputable def InfinityNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  sSup {y : ℝ | ∃ i : Fin n, y = |x i|}

noncomputable def VectorNorm {n : ℕ}
    (q : ExtendedExponent) (x : Fin n → ℝ) : ℝ :=
  match q with
  | .finite r => FiniteLpNorm r x
  | .infinity => InfinityNorm x

/-- Ordinary real matrix-vector product, including rectangular matrices. -/
def MatrixAction {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => ∑ j, B i j * x j

/-- The actual induced operator norm over every real input vector in the
ℓ_p unit ball. -/
noncomputable def OperatorNorm {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) ℝ)
    (p : ℝ) (q : ExtendedExponent) : ℝ :=
  sSup {y : ℝ | ∃ x : Fin n → ℝ,
    FiniteLpNorm p x ≤ 1 ∧ y = VectorNorm q (MatrixAction B x)}

/-- `p* = ∞` at `p=1`, and `p/(p-1)` otherwise. -/
noncomputable def ConjugateExponent (p : ℝ) : ExtendedExponent :=
  if p = 1 then .infinity else .finite (p / (p - 1))

def AdmissibleOutputExponent : ExtendedExponent → Prop
  | .finite q => 2 ≤ q
  | .infinity => True

/-- `min(∞,L)=L` at the infinity endpoint. -/
noncomputable def CappedExponent (q : ExtendedExponent) (L : ℝ) : ℝ :=
  match q with
  | .finite r => min r L
  | .infinity => L

/-- The exact natural-logarithmic cap `L(k)=max(1,ln k)`. -/
noncomputable def LogCap (k : ℕ) : ℝ :=
  max 1 (Real.log (k : ℝ))

/-- Independent standard real Gaussian entries, one per matrix coordinate. -/
noncomputable def GaussianLaw (m n : ℕ) :
    Measure ((Fin m × Fin n) → ℝ) :=
  Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1)

def WeightedGaussian {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (g : (Fin m × Fin n) → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => A i j * g (i, j)

/-- `D₁`: maximum ℓ_(p*) norm of an actual row of the variance profile. -/
noncomputable def RowScale {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (p : ℝ) : ℝ :=
  sSup {y : ℝ | ∃ i : Fin m,
    y = VectorNorm (ConjugateExponent p) (fun j => A i j)}

/-- `D₂`: maximum ℓ_q norm of an actual column. -/
noncomputable def ColumnScale {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (q : ExtendedExponent) : ℝ :=
  sSup {y : ℝ | ∃ j : Fin n,
    y = VectorNorm q (fun i => A i j)}

/-- Samplewise maximum of the absolute weighted Gaussian entries. -/
noncomputable def EntryMaximum {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (g : (Fin m × Fin n) → ℝ) : ℝ :=
  sSup {y : ℝ | ∃ i : Fin m, ∃ j : Fin n,
    y = |A i j * g (i, j)|}

noncomputable def ExpectedOperatorNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (p : ℝ) (q : ExtendedExponent) : ℝ :=
  ∫ g : (Fin m × Fin n) → ℝ,
    OperatorNorm (WeightedGaussian A g) p q ∂GaussianLaw m n

noncomputable def ExpectedEntryMaximum {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∫ g : (Fin m × Fin n) → ℝ, EntryMaximum A g ∂GaussianLaw m n

/-- One positive real constant works for all positive dimensions, all
`1≤p≤2≤q≤∞`, and every real variance profile. This is only the upper
bound from the original conjecture. -/
def Target : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ m n : ℕ, 0 < m → 0 < n →
      ∀ p : ℝ, 1 ≤ p → p ≤ 2 →
        ∀ q : ExtendedExponent, AdmissibleOutputExponent q →
          ∀ A : Matrix (Fin m) (Fin n) ℝ,
            ExpectedOperatorNorm A p q ≤ C *
              (Real.sqrt (CappedExponent (ConjugateExponent p) (LogCap n)) *
                  RowScale A p +
                Real.sqrt (CappedExponent q (LogCap m)) * ColumnScale A q +
                ExpectedEntryMaximum A)

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.Statements.MI31
