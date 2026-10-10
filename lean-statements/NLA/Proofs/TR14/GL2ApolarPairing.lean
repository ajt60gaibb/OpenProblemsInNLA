import NLA.Proofs.TR14.GL2MomentDual
import NLA.Proofs.TR14.ApolarMinimal

/-!
Exact unweighted apolar convolution as annihilation of every complementary
homogeneous product. No chart, width, or target claim is made.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open scoped BigOperators
noncomputable section

/-- Multiplication in complementary degrees `d+(D-d)=D`. -/
def binaryProductAt {D d : ℕ} (hd : d ≤ D) (G : BinaryForm d)
    (Q : BinaryForm (D - d)) : BinaryForm D :=
  ⟨G.1 * Q.1, by
    change (G.1 * Q.1).IsHomogeneous D
    simpa only [Nat.add_sub_of_le hd] using G.2.mul Q.2⟩

private theorem binaryProductAt_monomial {D d : ℕ} (hd : d ≤ D)
    (i : Fin (d + 1)) (j : Fin (D - d + 1)) :
    binaryProductAt hd (binaryMonomial d i) (binaryMonomial (D - d) j) =
      binaryMonomial D ⟨i.val + j.val, by
        have hi := i.isLt
        have hj := j.isLt
        omega⟩ := by
  apply Subtype.ext
  change ((MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ^ (d - i.val) *
      MvPolynomial.X 1 ^ i.val) *
    (MvPolynomial.X 0 ^ ((D - d) - j.val) * MvPolynomial.X 1 ^ j.val) =
    MvPolynomial.X 0 ^ (D - (i.val + j.val)) *
      MvPolynomial.X 1 ^ (i.val + j.val)
  have hexp : D - (i.val + j.val) =
      (d - i.val) + ((D - d) - j.val) := by
    have hi := i.isLt
    have hj := j.isLt
    omega
  rw [hexp, pow_add, pow_add]
  ring

/-- Testing against one complementary monomial is exactly one frozen
apolar convolution equation, including both endpoint shifts. -/
theorem homogeneousMoment_product_monomial {D d : ℕ} (hd : d ≤ D)
    (h : Fin (D + 1) → ℂ) (g : Fin (d + 1) → ℂ)
    (j : Fin (D - d + 1)) :
    homogeneousMoment h
      (binaryProductAt hd (binaryFormEquiv d g) (binaryMonomial (D - d) j)) =
      ∑ i : Fin (d + 1), g i * h ⟨i.val + j.val, by
        have hi := i.isLt
        have hj := j.isLt
        omega⟩ := by
  have hprod : binaryProductAt hd (binaryFormEquiv d g) (binaryMonomial (D - d) j) =
      ∑ i : Fin (d + 1), g i •
        binaryProductAt hd (binaryMonomial d i) (binaryMonomial (D - d) j) := by
    rw [binaryFormEquiv_eq_sum]
    apply Subtype.ext
    simp [binaryProductAt, Finset.sum_mul]
  rw [hprod, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [binaryProductAt_monomial, homogeneousMoment_monomial]

/-- The audited finite apolar predicate is annihilation of every
complementary homogeneous form, not merely selected monomial pairs. -/
theorem apolar_iff_product_annihilation {D d : ℕ} (hd : d ≤ D)
    (h : Fin (D + 1) → ℂ) (g : Fin (d + 1) → ℂ) :
    IsApolar h d hd g ↔
      ∀ Q : BinaryForm (D - d),
        homogeneousMoment h (binaryProductAt hd (binaryFormEquiv d g) Q) = 0 := by
  constructor
  · intro hAp Q
    let q := (binaryFormEquiv (D - d)).symm Q
    have hq : Q = ∑ j : Fin (D - d + 1), q j • binaryMonomial (D - d) j := by
      calc
        Q = binaryFormEquiv (D - d) q :=
          ((binaryFormEquiv (D - d)).apply_symm_apply Q).symm
        _ = _ := binaryFormEquiv_eq_sum (D - d) q
    have hprod : binaryProductAt hd (binaryFormEquiv d g) Q =
        ∑ j : Fin (D - d + 1), q j •
          binaryProductAt hd (binaryFormEquiv d g) (binaryMonomial (D - d) j) := by
      rw [hq]
      apply Subtype.ext
      simp [binaryProductAt, Finset.mul_sum]
    rw [hprod, map_sum]
    simp only [map_smul, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro j hj
    rw [homogeneousMoment_product_monomial hd h g j]
    change apolarMap h d hd g = 0 at hAp
    have hz := congrFun hAp j
    simp [apolarMap] at hz
    simp [hz]
  · intro hAnn
    change apolarMap h d hd g = 0
    apply funext
    intro j
    have hz := hAnn (binaryMonomial (D - d) j)
    rw [homogeneousMoment_product_monomial hd h g j] at hz
    simpa [apolarMap] using hz

#assert_trust kernel binaryProductAt
#assert_trust kernel homogeneousMoment_product_monomial
#assert_trust kernel apolar_iff_product_annihilation
#print axioms apolar_iff_product_annihilation

end
end NLA.Proofs.TR14
