import NLA.Statements.TR26

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

abbrev BinaryForm (R : Type*) [CommSemiring R] := MvPolynomial (Fin 2) R

/-- The original upper-triangle coordinate convention over a coefficient ring. -/
def coordinateEntry {R : Type*} {d : ℕ} (H : SymIndex d → R)
    (i j : Index d) : R :=
  if h : i ≤ j then H ⟨(i, j), h⟩
  else H ⟨(j, i), le_of_lt (lt_of_not_ge h)⟩

def affineDenominatorOver (R : Type*) [CommSemiring R] (d : ℕ) : Polynomial R :=
  ∑ i : Index d, Polynomial.X ^ (2 * i.val)

def affineNumeratorOver {R : Type*} [CommSemiring R] {d : ℕ}
    (H : SymIndex d → R) : Polynomial R :=
  ∑ i : Index d, ∑ j : Index d,
    Polynomial.C (coordinateEntry H i j) * Polynomial.X ^ (i.val + j.val)

def binaryVeroneseOver (R : Type*) [CommSemiring R] (d : ℕ)
    (i : Index d) : BinaryForm R :=
  MvPolynomial.X 0 ^ (d - i.val) * MvPolynomial.X 1 ^ i.val

def binaryDenominatorOver (R : Type*) [CommSemiring R] (d : ℕ) : BinaryForm R :=
  ∑ i : Index d, binaryVeroneseOver R d i * binaryVeroneseOver R d i

def binaryNumeratorOver {R : Type*} [CommSemiring R] {d : ℕ}
    (H : SymIndex d → R) : BinaryForm R :=
  ∑ i : Index d, ∑ j : Index d,
    MvPolynomial.C (coordinateEntry H i j) *
      binaryVeroneseOver R d i * binaryVeroneseOver R d j

def affineWronskianOver {R : Type*} [CommRing R] {d : ℕ}
    (H : SymIndex d → R) : Polynomial R :=
  (affineNumeratorOver H).derivative * affineDenominatorOver R d -
    affineNumeratorOver H * (affineDenominatorOver R d).derivative

/-- Fixed homogeneous degree `4*d-2`, retaining possible roots at infinity. -/
def binaryWronskianOver {R : Type*} [CommRing R] [Algebra ℂ R] {d : ℕ}
    (H : SymIndex d → R) : BinaryForm R :=
  MvPolynomial.C (algebraMap ℂ R ((2 * d : ℂ)⁻¹)) *
    (MvPolynomial.pderiv 1 (binaryNumeratorOver H) *
        MvPolynomial.pderiv 0 (binaryDenominatorOver R d) -
      MvPolynomial.pderiv 0 (binaryNumeratorOver H) *
        MvPolynomial.pderiv 1 (binaryDenominatorOver R d))

def binaryEvalOver {R : Type*} [CommSemiring R] (P : BinaryForm R) (a b : R) : R :=
  MvPolynomial.eval ![a, b] P

/-- Coefficient index counts the exponent of the second homogeneous variable. -/
def binaryCoeff {R : Type*} [CommSemiring R] (k : ℕ) (P : BinaryForm R) :
    Fin (k + 1) → R :=
  fun i => MvPolynomial.coeff
    (Finsupp.single 0 (k - i.val) + Finsupp.single 1 i.val) P

def wronskianCoefficientsOver {R : Type*} [CommRing R] [Algebra ℂ R] {d : ℕ}
    (H : SymIndex d → R) : Fin (4 * d - 2 + 1) → R :=
  binaryCoeff (4 * d - 2) (binaryWronskianOver H)

abbrev affineDenominator (d : ℕ) : Polynomial ℂ := affineDenominatorOver ℂ d
abbrev affineNumerator {d : ℕ} (H : Parameter d) : Polynomial ℂ := affineNumeratorOver H
abbrev affineWronskian {d : ℕ} (H : Parameter d) : Polynomial ℂ := affineWronskianOver H
abbrev binaryDenominator (d : ℕ) : BinaryForm ℂ := binaryDenominatorOver ℂ d
abbrev binaryNumerator {d : ℕ} (H : Parameter d) : BinaryForm ℂ := binaryNumeratorOver H
abbrev binaryWronskian {d : ℕ} (H : Parameter d) : BinaryForm ℂ := binaryWronskianOver H
abbrev binaryEval (P : BinaryForm ℂ) (a b : ℂ) : ℂ := binaryEvalOver P a b

theorem coordinateEntry_eq {d : ℕ} (H : Parameter d) (i j : Index d) :
    coordinateEntry H i j = symmetricEntry H i j := rfl

theorem binaryVeronese_eval (d : ℕ) (i : Index d) (a b : ℂ) :
    binaryEval (binaryVeroneseOver ℂ d i) a b = veronese d a b i := by
  simp [binaryEvalOver, binaryVeroneseOver, veronese]

theorem binaryDenominator_eval (d : ℕ) (a b : ℂ) :
    binaryEval (binaryDenominator d) a b = denominator (veronese d a b) := by
  simp [binaryEvalOver, binaryDenominatorOver, binaryVeroneseOver, denominator, veronese]

theorem binaryNumerator_eval {d : ℕ} (H : Parameter d) (a b : ℂ) :
    binaryEval (binaryNumerator H) a b = numerator H (veronese d a b) := by
  simp only [binaryEvalOver, binaryNumeratorOver, numerator, map_sum, map_mul,
    MvPolynomial.eval_C]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change coordinateEntry H i j * binaryEval (binaryVeroneseOver ℂ d i) a b *
    binaryEval (binaryVeroneseOver ℂ d j) a b = _
  rw [binaryVeronese_eval, binaryVeronese_eval, coordinateEntry_eq]
  ring

#assert_trust kernel binaryVeronese_eval
#assert_trust kernel binaryDenominator_eval
#assert_trust kernel binaryNumerator_eval
#print axioms binaryNumerator_eval
end NLA.Proofs.TR26
