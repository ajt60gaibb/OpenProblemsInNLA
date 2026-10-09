import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import NLA.Computation.Complexity
import NLA.Computation.BinaryEncoding

/-! The concrete rational-input, binary-encoded unrestricted static
output-feedback decision language shared by live and reviewed MF-08. -/
set_option autoImplicit false
open scoped BigOperators

namespace NLA.Statements.Shared.MF08Decision

open NLA.Computation.BinaryEncoding

/-- The three rational plant matrices and all dimensions are part of the
finite input. The validity condition below enforces positive dimensions. -/
structure Input where
  n : ℕ
  m : ℕ
  p : ℕ
  A : Matrix (Fin n) (Fin n) ℚ
  B : Matrix (Fin n) (Fin m) ℚ
  C : Matrix (Fin p) (Fin n) ℚ

def ValidInput (a : Input) : Prop := 0 < a.n ∧ 0 < a.m ∧ 0 < a.p

/-- Fixed self-delimiting binary dimension/rational encoding, with all
matrix entries in ordinary row-major order. Equality with this complete
word rules out a malformed prefix or an unchecked suffix. -/
def Encode (a : Input) : NLA.Computation.Word :=
  encodeNat a.n ++ encodeNat a.m ++ encodeNat a.p ++
    encodeRats ((List.ofFn (fun i : Fin a.n =>
      List.ofFn (fun j : Fin a.n => a.A i j))).flatten) ++
    encodeRats ((List.ofFn (fun i : Fin a.n =>
      List.ofFn (fun j : Fin a.m => a.B i j))).flatten) ++
    encodeRats ((List.ofFn (fun i : Fin a.p =>
      List.ofFn (fun j : Fin a.n => a.C i j))).flatten)

/-- Every feedback entry is an unrestricted real number. The nested finite
sums are exactly the entries of `A+B*K*C`. -/
def ClosedLoop (a : Input) (K : Matrix (Fin a.m) (Fin a.p) ℝ) :
    Matrix (Fin a.n) (Fin a.n) ℝ :=
  fun i j => (a.A i j : ℝ) +
    ∑ u : Fin a.m, ∑ v : Fin a.p,
      (a.B i u : ℝ) * K u v * (a.C v j : ℝ)

/-- Strict Hurwitz stability: every complex eigenvalue has negative real
part. Eigenvalues are characterized by actual nonzero complex eigenvectors,
so imaginary-axis and zero-real-part cases fail. -/
def Hurwitz {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ z : ℂ,
    (∃ x : Fin n → ℂ, x ≠ 0 ∧
      ∀ i : Fin n, (∑ j : Fin n, (M i j : ℂ) * x j) = z * x i) →
    z.re < 0

/-- Exact unrestricted rational-input decision language over finite binary
words. No gain bound, prescribed poles, or NP-membership assertion appears. -/
def DecisionLanguage : Set NLA.Computation.Word :=
  {w | ∃ a : Input, w = Encode a ∧ ValidInput a ∧
    ∃ K : Matrix (Fin a.m) (Fin a.p) ℝ, Hurwitz (ClosedLoop a K)}

end NLA.Statements.Shared.MF08Decision
