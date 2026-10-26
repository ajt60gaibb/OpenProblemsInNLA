import NLA.Proofs.TR26.FixedDiscriminantBinary
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! Exact fixed-size resultant identification and its projective zero set.
Leading coefficient loss is represented by a genuine common root at infinity. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace NLA.Proofs.TR26.BinaryDiscriminant

theorem shiftedCoeff_eq_ofFn {R : Type*} [CommSemiring R] [DecidableEq R]
    {k : ℕ} (hk : 0 < k) (p : Fin k → R) (r : SylvesterIndex k) (l : Fin (k - 1)) :
    shiftedCoeff k p r l = if r.val ∈ Set.Icc l.val (l.val + (k - 1)) then
      (Polynomial.ofFn k p).coeff (r.val - l.val) else 0 := by
  classical
  by_cases h : r.val ∈ Set.Icc l.val (l.val + (k - 1))
  · rw [if_pos h]
    have hj : r.val - l.val < k := by rcases h with ⟨hl, hu⟩; omega
    let j0 : Fin k := ⟨r.val - l.val, hj⟩
    rw [Polynomial.ofFn_coeff_eq_val_of_lt p hj]
    unfold shiftedCoeff
    rw [Finset.sum_eq_single j0]
    · have heq : r.val = l.val + j0.val := by have := h.1; dsimp [j0]; omega
      rw [if_pos heq]
    · intro j _ hjne
      have hne : r.val ≠ l.val + j.val := by
        intro heq
        apply hjne
        apply Fin.ext
        dsimp [j0]
        omega
      simp [hne]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro j _
    have hne : r.val ≠ l.val + j.val := by
      intro heq
      apply h
      have := j.isLt
      constructor <;> omega
    simp [hne]

theorem sylvesterMatrix_eq_polynomial {R : Type*} [CommRing R] [DecidableEq R]
    {k : ℕ} (hk : 0 < k) (c : Fin (k + 1) → R) :
    sylvesterMatrix k c = Polynomial.sylvester
      (Polynomial.ofFn k (partialBCoeff k c)) (Polynomial.ofFn k (partialACoeff k c))
      (k - 1) (k - 1) := by
  ext r i
  obtain ⟨z, rfl⟩ := finSumFinEquiv.surjective i
  cases z with
  | inl l =>
    simp only [sylvesterMatrix, Equiv.symm_apply_apply, Sum.elim_inl]
    rw [shiftedCoeff_eq_ofFn hk]
    simp only [Polynomial.sylvester, Matrix.of_apply, finSumFinEquiv_apply_left, Fin.addCases_left]
  | inr l =>
    simp only [sylvesterMatrix, Equiv.symm_apply_apply, Sum.elim_inr]
    rw [shiftedCoeff_eq_ofFn hk]
    simp only [Polynomial.sylvester, Matrix.of_apply, finSumFinEquiv_apply_right, Fin.addCases_right]

theorem eval_fixedDiscriminant_resultant {k : ℕ} (hk : 0 < k)
    (c : Fin (k + 1) → ℂ) :
    MvPolynomial.eval c (fixedDiscriminant k) =
      Polynomial.resultant (Polynomial.ofFn k (partialBCoeff k c))
        (Polynomial.ofFn k (partialACoeff k c)) (k - 1) (k - 1) := by
  rw [eval_fixedDiscriminant, sylvesterMatrix_eq_polynomial hk]
  rfl

theorem homogeneousEval_at_one (k : ℕ) (p : Fin k → ℂ) (z : ℂ) :
    (∑ j : Fin k, p j * (1 : ℂ) ^ (k - 1 - j.val) * z ^ j.val) =
      (Polynomial.ofFn k p).eval z := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp [Polynomial.eval_finsetSum]

theorem homogeneousEval_at_infinity {k : ℕ} (hk : 0 < k) (p : Fin k → ℂ) :
    (∑ j : Fin k, p j * (0 : ℂ) ^ (k - 1 - j.val) * (1 : ℂ) ^ j.val) =
      p ⟨k - 1, by omega⟩ := by
  classical
  let jt : Fin k := ⟨k - 1, by omega⟩
  rw [Finset.sum_eq_single jt]
  · simp [jt]
  · intro j _ hj
    have hne : k - 1 - j.val ≠ 0 := by
      have hj' : j.val ≠ k - 1 := by intro heq; apply hj; exact Fin.ext heq
      have := j.isLt
      omega
    simp [zero_pow hne]
  · simp

theorem common_root_of_resultant_zero_full_left (f g : Polynomial ℂ) (m n : ℕ)
    (hf : f.natDegree = m) (hf0 : f ≠ 0) (hg : g.natDegree ≤ n)
    (hres : Polynomial.resultant f g m n = 0) :
    ∃ z : ℂ, f.eval z = 0 ∧ g.eval z = 0 := by
  rw [← hf, Polynomial.resultant_eq_prod_eval f g n hg (IsAlgClosed.splits f)] at hres
  have hlead : f.leadingCoeff ^ n ≠ 0 := pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hf0)
  have hp : (f.roots.map g.eval).prod = 0 := (mul_eq_zero.mp hres).resolve_left hlead
  obtain ⟨z, hz, hgz⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
  exact ⟨z, Polynomial.isRoot_of_mem_roots hz, hgz⟩

theorem common_projective_root_of_resultant_zero {k : ℕ} (hk : 2 ≤ k)
    (p q : Fin k → ℂ)
    (hres : Polynomial.resultant (Polynomial.ofFn k p) (Polynomial.ofFn k q)
      (k - 1) (k - 1) = 0) :
    ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧
      (∑ j : Fin k, p j * a ^ (k - 1 - j.val) * b ^ j.val) = 0 ∧
      (∑ j : Fin k, q j * a ^ (k - 1 - j.val) * b ^ j.val) = 0 := by
  let jt : Fin k := ⟨k - 1, by omega⟩
  have hpbound : (Polynomial.ofFn k p).natDegree ≤ k - 1 :=
    Nat.le_sub_one_of_lt (Polynomial.ofFn_natDegree_lt (by omega) p)
  have hqbound : (Polynomial.ofFn k q).natDegree ≤ k - 1 :=
    Nat.le_sub_one_of_lt (Polynomial.ofFn_natDegree_lt (by omega) q)
  have hcoeff (v : Fin k → ℂ) : (Polynomial.ofFn k v).coeff (k - 1) = v jt :=
    Polynomial.ofFn_coeff_eq_val_of_lt v (by omega)
  have hfull (v : Fin k → ℂ) (hb : (Polynomial.ofFn k v).natDegree ≤ k - 1)
      (hnz : v jt ≠ 0) : (Polynomial.ofFn k v).natDegree = k - 1 ∧ Polynomial.ofFn k v ≠ 0 := by
    have hc : (Polynomial.ofFn k v).coeff (k - 1) ≠ 0 := by rwa [hcoeff]
    exact ⟨le_antisymm hb (Polynomial.le_natDegree_of_ne_zero hc),
      fun hz => hc (by rw [hz, Polynomial.coeff_zero])⟩
  by_cases hp : p jt = 0
  · by_cases hq : q jt = 0
    · refine ⟨0, 1, Or.inr one_ne_zero, ?_, ?_⟩
      · exact (homogeneousEval_at_infinity (by omega : 0 < k) p).trans hp
      · exact (homogeneousEval_at_infinity (by omega : 0 < k) q).trans hq
    · obtain ⟨hf, hf0⟩ := hfull q hqbound hq
      have hswap : Polynomial.resultant (Polynomial.ofFn k q) (Polynomial.ofFn k p)
          (k - 1) (k - 1) = 0 := by
        rw [Polynomial.resultant_comm, hres, mul_zero]
      obtain ⟨z, hqz, hpz⟩ := common_root_of_resultant_zero_full_left
        (Polynomial.ofFn k q) (Polynomial.ofFn k p) _ _ hf hf0 hpbound hswap
      exact ⟨1, z, Or.inl one_ne_zero, (homogeneousEval_at_one k p z).trans hpz,
        (homogeneousEval_at_one k q z).trans hqz⟩
  · obtain ⟨hf, hf0⟩ := hfull p hpbound hp
    obtain ⟨z, hpz, hqz⟩ := common_root_of_resultant_zero_full_left
      (Polynomial.ofFn k p) (Polynomial.ofFn k q) _ _ hf hf0 hqbound hres
    exact ⟨1, z, Or.inl one_ne_zero, (homogeneousEval_at_one k p z).trans hpz,
      (homogeneousEval_at_one k q z).trans hqz⟩

theorem eval_fixedDiscriminant_eq_zero_iff {k : ℕ} (hk : 2 ≤ k)
    (c : Fin (k + 1) → ℂ) :
    MvPolynomial.eval c (fixedDiscriminant k) = 0 ↔ HasMultipleProjectiveRoot k c := by
  constructor
  · intro hz
    rw [eval_fixedDiscriminant_resultant (by omega : 0 < k)] at hz
    obtain ⟨a, b, hab, hb, ha⟩ := common_projective_root_of_resultant_zero hk
      (partialBCoeff k c) (partialACoeff k c) hz
    exact ⟨a, b, hab, ha, hb⟩
  · exact multiple_projective_root_vanishes hk c


theorem eval_fixedDiscriminant_eq_zero_iff_actual_partials {k : ℕ} (hk : 2 ≤ k)
    (c : Fin (k + 1) → ℂ) :
    MvPolynomial.eval c (fixedDiscriminant k) = 0 ↔
      ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧
        binaryEval (pderiv 0 (binaryFromCoefficients k c)) a b = 0 ∧
        binaryEval (pderiv 1 (binaryFromCoefficients k c)) a b = 0 := by
  rw [eval_fixedDiscriminant_eq_zero_iff hk]
  simp only [HasMultipleProjectiveRoot, eval_partialA_binaryFromCoefficients,
    eval_partialB_binaryFromCoefficients]

theorem binaryValue_eq_zero_of_partials {k : ℕ} (hk : 0 < k)
    (c : Fin (k + 1) → ℂ) (a b : ℂ)
    (ha : binaryEval (pderiv 0 (binaryFromCoefficients k c)) a b = 0)
    (hb : binaryEval (pderiv 1 (binaryFromCoefficients k c)) a b = 0) :
    binaryValue k c a b = 0 := by
  have heuler := (binaryFromCoefficients_homogeneous k c).sum_X_mul_pderiv
  have heval := congrArg (MvPolynomial.eval ![a, b]) heuler
  simp only [map_sum, map_mul, eval_X, nsmul_eq_mul, map_natCast] at heval
  rw [Fin.sum_univ_two] at heval
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at heval
  change a * binaryEval (pderiv 0 (binaryFromCoefficients k c)) a b +
      b * binaryEval (pderiv 1 (binaryFromCoefficients k c)) a b =
      (k : ℂ) * binaryEval (binaryFromCoefficients k c) a b at heval
  rw [ha, hb, mul_zero, mul_zero, zero_add] at heval
  have hvalue : binaryEval (binaryFromCoefficients k c) a b = binaryValue k c a b :=
    binaryFromCoefficients_eval k c a b
  rw [hvalue] at heval
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  exact (mul_eq_zero.mp heval.symm).resolve_left hkC

#assert_trust kernel eval_fixedDiscriminant_resultant
#assert_trust kernel eval_fixedDiscriminant_eq_zero_iff_actual_partials
#assert_trust kernel binaryValue_eq_zero_of_partials
#assert_trust kernel common_projective_root_of_resultant_zero
#assert_trust kernel eval_fixedDiscriminant_eq_zero_iff
#print axioms eval_fixedDiscriminant_eq_zero_iff
#print axioms binaryValue_eq_zero_of_partials
end NLA.Proofs.TR26.BinaryDiscriminant
