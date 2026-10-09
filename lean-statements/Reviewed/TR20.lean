/- Frozen statement boundary. Changes reopen independent review. -/
import Mathlib
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! TR-20: the two reduced degrees of the nonisotropic Rayleigh–Ritz
critical-point discriminant in the full complex symmetric-matrix parameter
space. The complete source and reviewed specification are retained in
`docs/lean/statements/TR-20/`. This is a statement, not a proof. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.ReviewedStatements.TR20

/-- Ordinary Segre entry coordinates for an `m × n` rank-one matrix. -/
abbrev Entry (m n : ℕ) := Fin m × Fin n

/-- One coordinate for each unordered pair of Segre entries is exactly one
coordinate for each entry of a complex symmetric matrix. -/
abbrev SymmetricParameters (m n : ℕ) := Sym2 (Entry m n) → ℂ
abbrev ParameterPolynomial (m n : ℕ) := MvPolynomial (Sym2 (Entry m n)) ℂ

def symmetricMatrix {m n : ℕ} (h : SymmetricParameters m n) :
    Matrix (Entry m n) (Entry m n) ℂ :=
  fun i j => h (s(i, j))

def wave {m n : ℕ} (a : Fin m → ℂ) (b : Fin n → ℂ) : Entry m n → ℂ :=
  fun ij => a ij.1 * b ij.2

/-- The first variation of the Segre vector. -/
def waveFirst {m n : ℕ} (a u : Fin m → ℂ) (b v : Fin n → ℂ) :
    Entry m n → ℂ :=
  fun ij => u ij.1 * b ij.2 + a ij.1 * v ij.2

/-- The mixed second variation of the Segre vector. -/
def waveSecond {m n : ℕ} (u u' : Fin m → ℂ) (v v' : Fin n → ℂ) :
    Entry m n → ℂ :=
  fun ij => u ij.1 * v' ij.2 + u' ij.1 * v ij.2

/-- Complex-bilinear transpose pairing, with no conjugation. -/
def bilinear {ι : Type*} [Fintype ι] (x y : ι → ℂ) : ℂ :=
  ∑ i, x i * y i

/-- The symmetric bilinear form represented by all independent coordinates
of `H`, still with no conjugation. -/
def matrixBilinear {m n : ℕ} (h : SymmetricParameters m n)
    (x y : Entry m n → ℂ) : ℂ :=
  ∑ i, ∑ j, x i * symmetricMatrix h i j * y j

def numerator {m n : ℕ} (h : SymmetricParameters m n)
    (a : Fin m → ℂ) (b : Fin n → ℂ) : ℂ :=
  matrixBilinear h (wave a b) (wave a b)

def denominator {m n : ℕ} (a : Fin m → ℂ) (b : Fin n → ℂ) : ℂ :=
  bilinear (wave a b) (wave a b)

/-- On the nonisotropic locus this is the full projective tangent space:
`aᵀu=bᵀv=0` removes each radial direction. -/
def Tangent {m n : ℕ} (a : Fin m → ℂ) (b : Fin n → ℂ)
    (u : Fin m → ℂ) (v : Fin n → ℂ) : Prop :=
  bilinear a u = 0 ∧ bilinear b v = 0

/-- Vanishing of the differential of `(ψᵀHψ)/(ψᵀψ)` along the Segre variety.
The denominator differential is zero on these orthogonal tangent slices. -/
def Critical {m n : ℕ} (h : SymmetricParameters m n)
    (a : Fin m → ℂ) (b : Fin n → ℂ) : Prop :=
  ∀ (u : Fin m → ℂ) (v : Fin n → ℂ), Tangent a b u v →
    matrixBilinear h (wave a b) (waveFirst a u b v) = 0

/-- Numerator of one half of the bilinear Hessian of the quotient, multiplied
by the nonzero denominator. This includes the curvature term from the Segre
embedding, `waveSecond`. -/
def HessianNumerator {m n : ℕ} (h : SymmetricParameters m n)
    (a : Fin m → ℂ) (b : Fin n → ℂ)
    (u u' : Fin m → ℂ) (v v' : Fin n → ℂ) : ℂ :=
  denominator a b *
      (matrixBilinear h (waveFirst a u b v) (waveFirst a u' b v') +
        matrixBilinear h (wave a b) (waveSecond u u' v v')) -
    numerator h a b *
      (bilinear (waveFirst a u b v) (waveFirst a u' b v') +
        bilinear (wave a b) (waveSecond u u' v v'))

/-- Singularity of the restricted Hessian: a nonzero tangent direction is
in its radical against every tangent direction. -/
def Degenerate {m n : ℕ} (h : SymmetricParameters m n)
    (a : Fin m → ℂ) (b : Fin n → ℂ) : Prop :=
  ∃ (u : Fin m → ℂ) (v : Fin n → ℂ),
    Tangent a b u v ∧ (u ≠ 0 ∨ v ≠ 0) ∧
      ∀ (u' : Fin m → ℂ) (v' : Fin n → ℂ),
        Tangent a b u' v' → HessianNumerator h a b u u' v v' = 0

/-- The affine cone over the original nonisotropic critical-degenerate
incidence image, excluding the zero matrix before projectivization. -/
def HasNonisotropicDegenerateCritical {m n : ℕ}
    (h : SymmetricParameters m n) : Prop :=
  (∃ ij : Sym2 (Entry m n), h ij ≠ 0) ∧
    ∃ (a : Fin m → ℂ) (b : Fin n → ℂ),
      denominator a b ≠ 0 ∧ Critical h a b ∧ Degenerate h a b

/-- The exact vanishing ideal of the incidence image. Polynomials vanishing
here are precisely those vanishing on its Zariski closure. -/
def VanishesOnIncidence {m n : ℕ} (P : ParameterPolynomial m n) : Prop :=
  ∀ h : SymmetricParameters m n,
    HasNonisotropicDegenerateCritical h → MvPolynomial.eval h P = 0

/-- Concrete affine-cone construction of the Zariski closure in symmetric
parameter coordinates: common zeros of the entire vanishing ideal. -/
def InDiscriminantClosure {m n : ℕ} (h : SymmetricParameters m n) : Prop :=
  ∀ P : ParameterPolynomial m n,
    VanishesOnIncidence P → MvPolynomial.eval h P = 0

/-- A homogeneous principal *vanishing ideal* gives the reduced projective
hypersurface, not a possibly repeated eliminant. Since a vanishing ideal is
radical, its principal generator is square-free up to units. Its total
homogeneous degree is the reduced projective degree. -/
def HasReducedHypersurfaceDegree (m n degree : ℕ) : Prop :=
  ∃ D : ParameterPolynomial m n,
    D ≠ 0 ∧ ¬IsUnit D ∧ MvPolynomial.totalDegree D = degree ∧
      (∀ (t : ℂ) (h : SymmetricParameters m n),
        MvPolynomial.eval (fun ij => t * h ij) D =
          t ^ degree * MvPolynomial.eval h D) ∧
      ∀ P : ParameterPolynomial m n, VanishesOnIncidence P ↔ D ∣ P

/-- Both formulas for all `n≥2`, in the full symmetric-matrix parameter
space and with reduced projective degree. -/
def Target : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    HasReducedHypersurfaceDegree 2 n (24 * Nat.choose (n + 1) 3) ∧
    HasReducedHypersurfaceDegree 3 n (24 * n ^ 2 * Nat.choose n 2)

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.TR20
