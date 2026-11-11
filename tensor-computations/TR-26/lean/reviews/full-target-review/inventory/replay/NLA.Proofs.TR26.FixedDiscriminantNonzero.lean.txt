import NLA.Proofs.TR26.FixedDiscriminant

/-! Exact coefficient specialization and a nonzero fixed-degree witness. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace NLA.Proofs.TR26.BinaryDiscriminant

theorem map_sylvesterMatrix {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (k : ℕ) (c : Fin (k + 1) → R) :
    φ.mapMatrix (sylvesterMatrix k c) = sylvesterMatrix k (fun i => φ (c i)) := by
  ext r i
  change φ (sylvesterMatrix k c r i) = _
  unfold sylvesterMatrix
  cases finSumFinEquiv.symm i <;>
    simp [shiftedCoeff, partialACoeff, partialBCoeff, apply_ite]

theorem eval_fixedDiscriminant (k : ℕ) (c : Fin (k + 1) → ℂ) :
    MvPolynomial.eval c (fixedDiscriminant k) = (sylvesterMatrix k c).det := by
  unfold fixedDiscriminant
  rw [(MvPolynomial.eval c).map_det, map_sylvesterMatrix]
  simp only [eval_X]

/-- The fixed degree-k form a^k+b^k in coefficient coordinates. -/
def fermatCoefficients (k : ℕ) (i : Fin (k + 1)) : ℂ :=
  if i.val = 0 ∨ i.val = k then 1 else 0

theorem fermat_partialA {k : ℕ} (_hk : 0 < k) (j : Fin k) :
    partialACoeff k (fermatCoefficients k) j = if j.val = 0 then (k : ℂ) else 0 := by
  dsimp [partialACoeff, fermatCoefficients, lowerIndex]
  have hj : j.val ≠ k := Nat.ne_of_lt j.isLt
  by_cases hz : j.val = 0
  · simp [hz]
  · simp [hz, hj]

theorem fermat_partialB {k : ℕ} (hk : 0 < k) (j : Fin k) :
    partialBCoeff k (fermatCoefficients k) j =
      if j.val = k - 1 then (k : ℂ) else 0 := by
  dsimp [partialBCoeff, fermatCoefficients, upperIndex]
  have hz : j.val + 1 ≠ 0 := by omega
  by_cases hj : j.val = k - 1
  · have heq : j.val + 1 = k := by omega
    have hpred : k - 1 + 1 = k := by omega
    simp only [hj, hpred, or_true, if_true, mul_one]
  · have hne : j.val + 1 ≠ k := by omega
    simp [hj, hne]

theorem fermat_shiftedA {k : ℕ} (hk : 0 < k) (r : SylvesterIndex k)
    (l : Fin (k - 1)) :
    shiftedCoeff k (partialACoeff k (fermatCoefficients k)) r l =
      if r.val = l.val then (k : ℂ) else 0 := by
  let j0 : Fin k := ⟨0, hk⟩
  unfold shiftedCoeff
  rw [Finset.sum_eq_single j0]
  · simp [fermat_partialA hk, j0]
  · intro j _ hj
    have hj0 : j.val ≠ 0 := by intro hz; apply hj; exact Fin.ext hz
    simp [fermat_partialA hk, hj0]
  · simp

theorem fermat_shiftedB {k : ℕ} (hk : 0 < k) (r : SylvesterIndex k)
    (l : Fin (k - 1)) :
    shiftedCoeff k (partialBCoeff k (fermatCoefficients k)) r l =
      if r.val = l.val + (k - 1) then (k : ℂ) else 0 := by
  let jt : Fin k := ⟨k - 1, by omega⟩
  unfold shiftedCoeff
  rw [Finset.sum_eq_single jt]
  · simp [fermat_partialB hk, jt]
  · intro j _ hj
    have hjt : j.val ≠ k - 1 := by intro hz; apply hj; exact Fin.ext hz
    simp [fermat_partialB hk, hjt]
  · simp

theorem fermat_sylvesterMatrix {k : ℕ} (hk : 0 < k) :
    sylvesterMatrix k (fermatCoefficients k) = (k : ℂ) • (1 : Matrix (SylvesterIndex k) _ ℂ) := by
  ext r i
  obtain ⟨z, rfl⟩ := finSumFinEquiv.surjective i
  cases z with
  | inl l =>
    simp [sylvesterMatrix, fermat_shiftedA hk, Matrix.one_apply, Matrix.smul_apply,
      Fin.ext_iff, finSumFinEquiv_apply_left]
  | inr l =>
    simp only [sylvesterMatrix, Equiv.symm_apply_apply, Sum.elim_inr]
    simp [fermat_shiftedB hk, Matrix.one_apply, Matrix.smul_apply,
      Fin.ext_iff, finSumFinEquiv_apply_right]

theorem eval_fermat_fixedDiscriminant {k : ℕ} (hk : 0 < k) :
    MvPolynomial.eval (fermatCoefficients k) (fixedDiscriminant k) =
      (k : ℂ) ^ (2 * k - 2) := by
  rw [eval_fixedDiscriminant, fermat_sylvesterMatrix hk, Matrix.det_smul]
  simp only [Matrix.det_one, mul_one, SylvesterIndex, Fintype.card_fin]
  congr 1
  omega

theorem fixedDiscriminant_ne_zero {k : ℕ} (hk : 2 ≤ k) : fixedDiscriminant k ≠ 0 := by
  intro hzero
  have h := eval_fermat_fixedDiscriminant (by omega : 0 < k)
  rw [hzero, map_zero] at h
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  exact (pow_ne_zero _ hkC) h.symm

theorem fixedDiscriminant_totalDegree {k : ℕ} (hk : 2 ≤ k) :
    (fixedDiscriminant k).totalDegree = 2 * k - 2 :=
  (fixedDiscriminant_homogeneous k).totalDegree (fixedDiscriminant_ne_zero hk)

#assert_trust kernel eval_fixedDiscriminant
#assert_trust kernel fixedDiscriminant_ne_zero
#assert_trust kernel fixedDiscriminant_totalDegree
#print axioms fixedDiscriminant_ne_zero
#print axioms fixedDiscriminant_totalDegree
end NLA.Proofs.TR26.BinaryDiscriminant
