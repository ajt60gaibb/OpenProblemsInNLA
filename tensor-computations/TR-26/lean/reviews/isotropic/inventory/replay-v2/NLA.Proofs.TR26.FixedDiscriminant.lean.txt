import NLA.Statements.TR26

/-! A fixed-size binary discriminant, formed as the Sylvester determinant of
both homogeneous partials. Its coefficient index counts the power of the second
binary variable. No specialized univariate leading coefficient is inverted. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace NLA.Proofs.TR26.BinaryDiscriminant

abbrev CoeffRing (k : ℕ) := MvPolynomial (Fin (k + 1)) ℂ
abbrev SylvesterIndex (k : ℕ) := Fin ((k - 1) + (k - 1))

def lowerIndex {k : ℕ} (j : Fin k) : Fin (k + 1) := ⟨j.val, by omega⟩
def upperIndex {k : ℕ} (j : Fin k) : Fin (k + 1) := ⟨j.val + 1, by omega⟩

/-- Coefficients of the first homogeneous partial of a binary degree-k form. -/
def partialACoeff {R : Type*} [CommSemiring R] (k : ℕ) (c : Fin (k + 1) → R)
    (j : Fin k) : R := (k - j.val : ℕ) * c (lowerIndex j)

/-- Coefficients of the second homogeneous partial, with the same fixed degree. -/
def partialBCoeff {R : Type*} [CommSemiring R] (k : ℕ) (c : Fin (k + 1) → R)
    (j : Fin k) : R := (j.val + 1 : ℕ) * c (upperIndex j)

/-- One coefficient of the product with a multiplier monomial. -/
def shiftedCoeff {R : Type*} [CommSemiring R] (k : ℕ) (p : Fin k → R)
    (r : SylvesterIndex k) (l : Fin (k - 1)) : R :=
  ∑ j : Fin k, if r.val = l.val + j.val then p j else 0

/-- Fixed homogeneous Sylvester matrix of both degree-(k-1) partials. -/
def sylvesterMatrix {R : Type*} [CommSemiring R] (k : ℕ) (c : Fin (k + 1) → R) :
    Matrix (SylvesterIndex k) (SylvesterIndex k) R :=
  fun r i => Sum.elim
    (fun l => shiftedCoeff k (partialACoeff k c) r l)
    (fun l => shiftedCoeff k (partialBCoeff k c) r l)
    (finSumFinEquiv.symm i)

/-- A universal polynomial in all k+1 binary coefficients. It differs from the
usual normalized binary discriminant by a nonzero scalar when k≥2. -/
def fixedDiscriminant (k : ℕ) : CoeffRing k :=
  (sylvesterMatrix k (fun i => X i : Fin (k + 1) → CoeffRing k)).det

/-- The actual homogeneous binary form, including its value at infinity. -/
def binaryValue {R : Type*} [CommSemiring R] (k : ℕ) (c : Fin (k + 1) → R)
    (a b : R) : R := ∑ i : Fin (k + 1), c i * a ^ (k - i.val) * b ^ i.val

/-- A multiple projective root of the actual fixed-degree binary form. -/
def HasMultipleProjectiveRoot (k : ℕ) (c : Fin (k + 1) → ℂ) : Prop :=
  ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧
    (∑ j : Fin k, partialACoeff k c j * a ^ (k - 1 - j.val) * b ^ j.val) = 0 ∧
    (∑ j : Fin k, partialBCoeff k c j * a ^ (k - 1 - j.val) * b ^ j.val) = 0

theorem partialA_homogeneous (k : ℕ) (j : Fin k) :
    (partialACoeff k (fun i => X i : Fin (k + 1) → CoeffRing k) j).IsHomogeneous 1 := by
  simpa only [partialACoeff, map_natCast] using
    isHomogeneous_C_mul_X (((k - j.val : ℕ) : ℂ)) (lowerIndex j)

theorem partialB_homogeneous (k : ℕ) (j : Fin k) :
    (partialBCoeff k (fun i => X i : Fin (k + 1) → CoeffRing k) j).IsHomogeneous 1 := by
  simpa only [partialBCoeff, map_natCast] using
    isHomogeneous_C_mul_X (((j.val + 1 : ℕ) : ℂ)) (upperIndex j)

theorem sylvester_entry_homogeneous (k : ℕ) (r i : SylvesterIndex k) :
    (sylvesterMatrix k (fun i => X i : Fin (k + 1) → CoeffRing k) r i).IsHomogeneous 1 := by
  unfold sylvesterMatrix
  cases finSumFinEquiv.symm i with
  | inl l =>
    simp only [Sum.elim_inl, shiftedCoeff]
    apply IsHomogeneous.sum
    intro j _
    split_ifs
    · exact partialA_homogeneous k j
    · exact isHomogeneous_zero _ _ 1
  | inr l =>
    simp only [Sum.elim_inr, shiftedCoeff]
    apply IsHomogeneous.sum
    intro j _
    split_ifs
    · exact partialB_homogeneous k j
    · exact isHomogeneous_zero _ _ 1

theorem fixedDiscriminant_homogeneous (k : ℕ) :
    (fixedDiscriminant k).IsHomogeneous (2 * k - 2) := by
  unfold fixedDiscriminant
  rw [Matrix.det_apply]
  have hcard : Fintype.card (SylvesterIndex k) = 2 * k - 2 := by
    simp only [SylvesterIndex, Fintype.card_fin]
    omega
  apply IsHomogeneous.sum
  intro σ _
  have hprod : (∏ i, sylvesterMatrix k (fun i => X i : Fin (k + 1) → CoeffRing k)
      (σ i) i).IsHomogeneous (2 * k - 2) := by
    convert IsHomogeneous.prod Finset.univ _ (fun _ => 1)
      (fun i _ => sylvester_entry_homogeneous k (σ i) i) using 1
    simp [hcard]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign
  · simpa only [hsign, one_smul] using hprod
  · simpa only [hsign, Units.neg_smul, one_smul] using hprod.neg

#assert_trust kernel fixedDiscriminant_homogeneous
#print axioms fixedDiscriminant_homogeneous
end NLA.Proofs.TR26.BinaryDiscriminant
