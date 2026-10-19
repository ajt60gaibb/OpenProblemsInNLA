import NLA.Proofs.TR14.TR14BinaryPencil

/-! The concrete squarefree apolar polynomial used in the binary upper
construction. Every recurrence is guarded by its actual available moment bound. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial
open scoped BigOperators Polynomial
noncomputable section

/-- Expand the actual quotient functional at a shifted polynomial, using
only moments whose indices lie in the supplied finite vector. -/
theorem binary_quotient_moment_expansion {D : ℕ}
    (h : Fin (D + 1) → ℂ) (g : ℂ[X]) (hg : g.Monic)
    (hrD : g.natDegree ≤ D) (hrec : MonicMomentRecurrence h g)
    (p : ℂ[X]) (k : ℕ) (hk : k + p.natDegree ≤ D) :
    quotientMomentFunctional h g hg hrD
      ((AdjoinRoot.root g) ^ k * AdjoinRoot.mk g p) =
      ∑ i : Fin (p.natDegree + 1), p.coeff i.val *
        h ⟨k + i.val, by have hi := i.isLt; omega⟩ := by
  have heval : AdjoinRoot.mk g p =
      ∑ i : Fin (p.natDegree + 1), p.coeff i.val • (AdjoinRoot.root g) ^ i.val := by
    rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_eq_sum_range]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  rw [heval, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [mul_smul_comm, map_smul]
  change p.coeff i.val *
      quotientMomentFunctional h g hg hrD
        ((AdjoinRoot.root g) ^ k * (AdjoinRoot.root g) ^ i.val) = _
  rw [← pow_add]
  rw [quotientMomentFunctional_all h g hg hrD hrec ⟨k + i.val, by
    have hi := i.isLt
    omega⟩]

/-- Quotient annihilation of every available shift proves the literal
monic moment recurrence, including the vacuous degree-D+1 case. -/
theorem binary_monicRecurrence_of_annihilation {D : ℕ}
    (h : Fin (D + 1) → ℂ) (g : ℂ[X]) (hg : g.Monic)
    (hrD : g.natDegree ≤ D) (hrec : MonicMomentRecurrence h g)
    (P : ℂ[X]) (hP : P.Monic)
    (hz : ∀ k : ℕ, k + P.natDegree ≤ D →
      quotientMomentFunctional h g hg hrD
        ((AdjoinRoot.root g) ^ k * AdjoinRoot.mk g P) = 0) :
    MonicMomentRecurrence h P := by
  intro k hk
  have hs := (binary_quotient_moment_expansion h g hg hrD hrec P k hk).symm.trans (hz k hk)
  rw [Fin.sum_univ_castSucc] at hs
  simp only [Fin.val_castSucc, Fin.val_last, hP.coeff_natDegree, one_mul] at hs
  apply eq_neg_of_add_eq_zero_left
  simpa only [add_comm] using hs

/-- Increase the modulus to any requested positive degree while retaining
coprimality with its actual inverse representative. -/
theorem binary_coprime_monic_multiple (g b : ℂ[X]) (hg : g.Monic)
    (hb0 : b ≠ 0) (hcop : IsCoprime b g) (v : ℕ) (hrv : g.natDegree ≤ v) :
    ∃ A : ℂ[X], A.Monic ∧ A.natDegree = v ∧ g ∣ A ∧ IsCoprime b A := by
  classical
  obtain ⟨a, ha⟩ := b.roots.toFinset.exists_notMem
  have hba : b.eval a ≠ 0 := by
    intro hz
    exact ha (Multiset.mem_toFinset.mpr ((mem_roots hb0).mpr hz))
  let q := (X - C a) ^ (v - g.natDegree)
  have hq : q.Monic := (monic_X_sub_C a).pow _
  let A := g * q
  have hA : A.Monic := hg.mul hq
  have hdeg : A.natDegree = v := by
    rw [show A = g * q from rfl, natDegree_mul hg.ne_zero hq.ne_zero]
    simp only [q, natDegree_pow, natDegree_X_sub_C, Nat.mul_one]
    omega
  refine ⟨A, hA, hdeg, dvd_mul_right g q, ?_⟩
  apply hcop.mul_right
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ b q).mpr
  intro α
  by_cases hroot : b.eval α ≠ 0
  · left
    simpa using hroot
  · right
    have hα : α ≠ a := by
      intro heq
      exact hba (heq ▸ not_ne_iff.mp hroot)
    simpa [q] using pow_ne_zero (v - g.natDegree) (sub_ne_zero.mpr hα)

/-- A least-apolar monic modulus supplies an actual monic separable
polynomial at degree D-r+2 with the exact bounded moment recurrence. -/
theorem binary_separable_apolar_polynomial {D : ℕ}
    (h : Fin (D + 1) → ℂ) (hh : h ≠ 0) (g : ℂ[X])
    (hg : g.Monic) (hrPos : 1 ≤ g.natDegree) (hrD : g.natDegree ≤ D)
    (hrHi : g.natDegree ≤ D / 2 + 1)
    (hAp : IsApolar h g.natDegree hrD
      (fun i : Fin (g.natDegree + 1) => g.coeff i.val))
    (hmin : ∀ d : ℕ, ∀ hd : d ≤ D, d < g.natDegree →
      ∀ b : Fin (d + 1) → ℂ, IsApolar h d hd b → b = 0) :
    ∃ P : ℂ[X], P.Monic ∧ P.natDegree = D - g.natDegree + 2 ∧
      P.Separable ∧ MonicMomentRecurrence h P := by
  obtain ⟨b, hb0, hbdeg, hcop, hbann⟩ :=
    binary_inverse_polynomial h hh g hg hrPos hrD hAp hmin
  let v := D - g.natDegree + 2
  have hrv : g.natDegree ≤ v := by dsimp [v]; omega
  obtain ⟨A, hA, hAdeg, hAdvd, hbA⟩ :=
    binary_coprime_monic_multiple g b hg hb0 hcop v hrv
  obtain ⟨c, _hc, hP, hPdeg, hPsep⟩ :=
    binary_monic_separable_pencil b A hA (by rw [hAdeg]; dsimp [v]; omega)
      (hbdeg.trans_le (by rw [hAdeg]; exact hrv)) hbA
  let P := A + C c * b
  have hdegree : P.natDegree = v := hPdeg.trans hAdeg
  refine ⟨P, hP, hdegree, hPsep, ?_⟩
  have hrec := monicMomentRecurrence_of_apolar h g hg hrD hAp
  apply binary_monicRecurrence_of_annihilation h g hg hrD hrec P hP
  intro k hk
  have hklow : k < g.natDegree - 1 := by rw [hdegree] at hk; dsimp [v] at hk; omega
  have hAzero : AdjoinRoot.mk g A = 0 := AdjoinRoot.mk_eq_zero.mpr hAdvd
  have hmkP : AdjoinRoot.mk g P = c • AdjoinRoot.mk g b := by
    simp only [P, map_add, map_mul, hAzero, zero_add]
    rw [AdjoinRoot.mk_C]
    exact (Algebra.smul_def c (AdjoinRoot.mk g b)).symm
  rw [hmkP, mul_smul_comm, map_smul, hbann k hklow, smul_zero]

#assert_trust kernel binary_quotient_moment_expansion
#assert_trust kernel binary_monicRecurrence_of_annihilation
#assert_trust kernel binary_coprime_monic_multiple
#assert_trust kernel binary_separable_apolar_polynomial
#print axioms binary_separable_apolar_polynomial

end
end NLA.Proofs.TR14
