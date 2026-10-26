import NLA.Proofs.TR26.FixedDiscriminantNonzero

/-! Projective-root support of the fixed homogeneous partial resultant. The
nonzero evaluation covector also covers the chart at infinity without division. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace NLA.Proofs.TR26.BinaryDiscriminant

def evaluationCovector (k : ℕ) (a b : ℂ) (r : SylvesterIndex k) : ℂ :=
  a ^ ((k - 1) + (k - 1) - 1 - r.val) * b ^ r.val

theorem contract_shiftedCoeff {k : ℕ} (hk : 2 ≤ k) (p : Fin k → ℂ)
    (a b : ℂ) (l : Fin (k - 1)) :
    (∑ r : SylvesterIndex k, evaluationCovector k a b r * shiftedCoeff k p r l) =
      (a ^ (k - 2 - l.val) * b ^ l.val) *
        ∑ j : Fin k, p j * a ^ (k - 1 - j.val) * b ^ j.val := by
  unfold shiftedCoeff
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  let rj : SylvesterIndex k := ⟨l.val + j.val, by have := l.isLt; have := j.isLt; omega⟩
  rw [Finset.sum_eq_single rj]
  · dsimp only [rj, evaluationCovector]
    rw [if_pos rfl]
    have hexp : (k - 1) + (k - 1) - 1 - (l.val + j.val) =
        (k - 2 - l.val) + (k - 1 - j.val) := by
      have := l.isLt
      have := j.isLt
      omega
    rw [hexp, pow_add, pow_add]
    ring
  · intro r _ hr
    have hne : r.val ≠ l.val + j.val := by
      intro heq
      apply hr
      exact Fin.ext heq
    simp [hne]
  · simp

theorem evaluationCovector_ne_zero {k : ℕ} (hk : 2 ≤ k) {a b : ℂ}
    (hab : a ≠ 0 ∨ b ≠ 0) : evaluationCovector k a b ≠ 0 := by
  intro hz
  have hsize : 0 < (k - 1) + (k - 1) := by omega
  rcases hab with ha | hb
  · let r0 : SylvesterIndex k := ⟨0, hsize⟩
    have h := congrFun hz r0
    simp only [evaluationCovector, r0, Nat.sub_zero, pow_zero, mul_one,
      Pi.zero_apply] at h
    exact (pow_ne_zero _ ha) h
  · let rt : SylvesterIndex k := ⟨(k - 1) + (k - 1) - 1, by omega⟩
    have h := congrFun hz rt
    simp only [evaluationCovector, rt, Nat.sub_self, pow_zero, one_mul,
      Pi.zero_apply] at h
    exact (pow_ne_zero _ hb) h

theorem multiple_projective_root_vanishes {k : ℕ} (hk : 2 ≤ k)
    (c : Fin (k + 1) → ℂ) (hroot : HasMultipleProjectiveRoot k c) :
    MvPolynomial.eval c (fixedDiscriminant k) = 0 := by
  obtain ⟨a, b, hab, ha, hb⟩ := hroot
  rw [eval_fixedDiscriminant]
  apply Matrix.exists_vecMul_eq_zero_iff.mp
  refine ⟨evaluationCovector k a b, evaluationCovector_ne_zero hk hab, ?_⟩
  ext i
  change (∑ r, evaluationCovector k a b r * sylvesterMatrix k c r i) = 0
  unfold sylvesterMatrix
  cases finSumFinEquiv.symm i with
  | inl l =>
    simp only [Sum.elim_inl]
    rw [contract_shiftedCoeff hk, ha, mul_zero]
  | inr l =>
    simp only [Sum.elim_inr]
    rw [contract_shiftedCoeff hk, hb, mul_zero]

#assert_trust kernel contract_shiftedCoeff
#assert_trust kernel evaluationCovector_ne_zero
#assert_trust kernel multiple_projective_root_vanishes
#print axioms multiple_projective_root_vanishes
end NLA.Proofs.TR26.BinaryDiscriminant
