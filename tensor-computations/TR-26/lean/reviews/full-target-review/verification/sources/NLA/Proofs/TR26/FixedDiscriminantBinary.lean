import NLA.Proofs.TR26.FixedDiscriminantRoots
import NLA.Proofs.TR26.BinaryDefinitions

/-! Bridge from fixed binary coefficients to genuine two-variable polynomial
partials, with the same a/b convention as the actual Wronskian family. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace NLA.Proofs.TR26.BinaryDiscriminant

def binaryFromCoefficients {R : Type*} [CommSemiring R] (k : ℕ)
    (c : Fin (k + 1) → R) : BinaryForm R :=
  ∑ i : Fin (k + 1), C (c i) * X 0 ^ (k - i.val) * X 1 ^ i.val

theorem binaryFromCoefficients_eval {R : Type*} [CommSemiring R] (k : ℕ)
    (c : Fin (k + 1) → R) (a b : R) :
    binaryEvalOver (binaryFromCoefficients k c) a b = binaryValue k c a b := by
  simp [binaryEvalOver, binaryFromCoefficients, binaryValue]

theorem binaryFromCoefficients_homogeneous {R : Type*} [CommSemiring R] (k : ℕ)
    (c : Fin (k + 1) → R) : (binaryFromCoefficients k c).IsHomogeneous k := by
  apply IsHomogeneous.sum
  intro i _
  convert ((isHomogeneous_X R (0 : Fin 2)).pow (k - i.val)).C_mul (c i) |>.mul
    ((isHomogeneous_X R (1 : Fin 2)).pow i.val) using 1
  have := i.isLt
  omega

theorem binaryFromCoefficients_partialA {R : Type*} [CommSemiring R] (k : ℕ)
    (c : Fin (k + 1) → R) :
    pderiv 0 (binaryFromCoefficients k c) =
      ∑ j : Fin k, C (partialACoeff k c j) * X 0 ^ (k - 1 - j.val) * X 1 ^ j.val := by
  unfold binaryFromCoefficients
  rw [map_sum, Fin.sum_univ_castSucc]
  simp [pderiv_X]
  apply Finset.sum_congr rfl
  intro j _
  have hindex : j.castSucc = lowerIndex j := Fin.ext rfl
  rw [hindex]
  simp only [partialACoeff, map_mul, map_natCast]
  have hexp : k - j.val - 1 = k - 1 - j.val := by omega
  rw [hexp]
  ring

theorem binaryFromCoefficients_partialB {R : Type*} [CommSemiring R] (k : ℕ)
    (c : Fin (k + 1) → R) :
    pderiv 1 (binaryFromCoefficients k c) =
      ∑ j : Fin k, C (partialBCoeff k c j) * X 0 ^ (k - 1 - j.val) * X 1 ^ j.val := by
  unfold binaryFromCoefficients
  rw [map_sum, Fin.sum_univ_succ]
  simp [pderiv_X]
  apply Finset.sum_congr rfl
  intro j _
  have hindex : j.succ = upperIndex j := Fin.ext rfl
  rw [hindex]
  simp only [partialBCoeff, map_mul, map_natCast]
  have hexp : k - (j.val + 1) = k - 1 - j.val := by omega
  rw [hexp]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem eval_partialA_binaryFromCoefficients (k : ℕ) (c : Fin (k + 1) → ℂ) (a b : ℂ) :
    binaryEval (pderiv 0 (binaryFromCoefficients k c)) a b =
      ∑ j : Fin k, partialACoeff k c j * a ^ (k - 1 - j.val) * b ^ j.val := by
  rw [binaryFromCoefficients_partialA]
  simp [binaryEvalOver]

theorem eval_partialB_binaryFromCoefficients (k : ℕ) (c : Fin (k + 1) → ℂ) (a b : ℂ) :
    binaryEval (pderiv 1 (binaryFromCoefficients k c)) a b =
      ∑ j : Fin k, partialBCoeff k c j * a ^ (k - 1 - j.val) * b ^ j.val := by
  rw [binaryFromCoefficients_partialB]
  simp [binaryEvalOver]

theorem eval_fixedDiscriminant_eq_zero_of_actual_partials {k : ℕ} (hk : 2 ≤ k)
    (c : Fin (k + 1) → ℂ) (a b : ℂ) (hab : a ≠ 0 ∨ b ≠ 0)
    (ha : binaryEval (pderiv 0 (binaryFromCoefficients k c)) a b = 0)
    (hb : binaryEval (pderiv 1 (binaryFromCoefficients k c)) a b = 0) :
    MvPolynomial.eval c (fixedDiscriminant k) = 0 := by
  apply multiple_projective_root_vanishes hk c
  exact ⟨a, b, hab, (eval_partialA_binaryFromCoefficients k c a b).symm.trans ha,
    (eval_partialB_binaryFromCoefficients k c a b).symm.trans hb⟩

#assert_trust kernel binaryFromCoefficients_homogeneous
#assert_trust kernel binaryFromCoefficients_partialA
#assert_trust kernel binaryFromCoefficients_partialB
#assert_trust kernel eval_fixedDiscriminant_eq_zero_of_actual_partials
#print axioms eval_fixedDiscriminant_eq_zero_of_actual_partials
end NLA.Proofs.TR26.BinaryDiscriminant
