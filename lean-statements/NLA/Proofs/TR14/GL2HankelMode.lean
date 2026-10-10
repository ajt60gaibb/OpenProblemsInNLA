import NLA.Proofs.TR14.GL2ApolarTransport

/-!
The exact zero-based multilinear Hankel pairing and its chart transport.
This module makes no width, rank, or frozen Target claim.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open NLA.Statements.TR14 MvPolynomial
open scoped BigOperators
noncomputable section

/-- Product of `m` genuine degree-`q` binary forms, including `m=0`. -/
def modeFormProduct (m q : ℕ) (u : Fin m → Fin (q + 1) → ℂ) : BinaryForm (m * q) :=
  ⟨∏ k : Fin m, (binaryFormEquiv q (u k)).1, by
    convert IsHomogeneous.prod (Finset.univ : Finset (Fin m))
      (fun k => (binaryFormEquiv q (u k)).1) (fun _ => q)
      (fun k _ => (binaryFormEquiv q (u k)).2) using 1; simp⟩

/-- The exact zero-based moment index for `m` modes of degree `q`. -/
def modeIndex {m q : ℕ} (i : Fin m → Fin (q + 1)) : Fin (m * q + 1) :=
  HankelIndex i

private theorem sum_binaryExponent_eq {m q : ℕ} (i : Fin m → Fin (q + 1)) :
    (∑ k : Fin m, binaryExponent q (i k)) = binaryExponent (m * q) (modeIndex i) := by
  apply Finsupp.ext
  intro a
  fin_cases a
  · simp only [Finsupp.finsetSum_apply]
    have hi : ∑ k : Fin m, (q - (i k).val) + ∑ k : Fin m, (i k).val = m * q := by
      rw [← Finset.sum_add_distrib]
      simp [Nat.sub_add_cancel (Nat.lt_succ_iff.mp (i _).isLt)]
    change (∑ k : Fin m, (q - (i k).val)) =
      m * q - (∑ k : Fin m, (i k).val)
    omega
  · simp [modeIndex, HankelIndex, binaryExponent]

private theorem binaryMonomial_eq_monomial (q : ℕ) (i : Fin (q + 1)) :
    (binaryMonomial q i).1 = MvPolynomial.monomial (binaryExponent q i) (1 : ℂ) := by
  change (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ^ (q - i.val) *
    MvPolynomial.X 1 ^ i.val = _
  rw [MvPolynomial.monomial_fin_two]
  simp [binaryExponent]

private theorem binaryFormEquiv_val_eq_sum_monomial (q : ℕ)
    (v : Fin (q + 1) → ℂ) :
    (binaryFormEquiv q v).1 =
      ∑ i : Fin (q + 1), MvPolynomial.monomial (binaryExponent q i) (v i) := by
  rw [binaryFormEquiv_eq_sum]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [binaryMonomial_eq_monomial]
  simp only [MvPolynomial.smul_monomial]
  simp

/-- Expansion of the full product uses each zero-based multi-index once,
with no multinomial factor. -/
theorem modeFormProduct_eq_sum (m q : ℕ) (u : Fin m → Fin (q + 1) → ℂ) :
    modeFormProduct m q u =
      ∑ i : Fin m → Fin (q + 1),
        (∏ k : Fin m, u k (i k)) • binaryMonomial (m * q) (modeIndex i) := by
  apply Subtype.ext
  simp only [modeFormProduct, Submodule.coe_sum]
  simp_rw [binaryFormEquiv_val_eq_sum_monomial]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← MvPolynomial.monomial_sum_prod, sum_binaryExponent_eq]
  simp [binaryMonomial_eq_monomial,
    MvPolynomial.smul_monomial, smul_eq_mul]

/-- The frozen Hankel tensor is exactly the multilinear moment pairing. -/
theorem hankel_multilinear_pairing (m q : ℕ)
    (h : Fin (m * q + 1) → ℂ) (u : Fin m → Fin (q + 1) → ℂ) :
    homogeneousMoment h (modeFormProduct m q u) =
      ∑ i : Fin m → Fin (q + 1),
        Hankel h i * ∏ k : Fin m, u k (i k) := by
  rw [modeFormProduct_eq_sum, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [homogeneousMoment_monomial]
  simp only [modeIndex, Hankel]
  ring

/-- Genuine substitution distributes over every mode product. -/
theorem chartPhi_modeFormProduct (z : ℂ) (m q : ℕ)
    (u : Fin m → Fin (q + 1) → ℂ) :
    chartPhi z (m * q) (modeFormProduct m q u) =
      modeFormProduct m q (fun k => chartCoefficientEquiv z q (u k)) := by
  apply Subtype.ext
  change (chartSubst z) (∏ k : Fin m, (binaryFormEquiv q (u k)).1) =
    ∏ k : Fin m, (binaryFormEquiv q (chartCoefficientEquiv z q (u k))).1
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro k hk
  exact congrArg Subtype.val
    (binaryFormEquiv_transportedApolarVector z q (u k)).symm

/-- The same invertible coefficient chart acts in all modes of the exact
frozen Hankel tensor; the moment chart is inverse dual. -/
theorem chart_hankel_multilinear (z : ℂ) (m q : ℕ)
    (h : Fin (m * q + 1) → ℂ) (u : Fin m → Fin (q + 1) → ℂ) :
    (∑ i : Fin m → Fin (q + 1),
      Hankel (transformedMoments z h) i *
        ∏ k : Fin m, chartCoefficientEquiv z q (u k) (i k)) =
      ∑ i : Fin m → Fin (q + 1),
        Hankel h i * ∏ k : Fin m, u k (i k) := by
  rw [← hankel_multilinear_pairing,
    ← hankel_multilinear_pairing,
    homogeneousMoment_transformedMoments]
  rw [← chartPhi_modeFormProduct]
  exact congrArg (homogeneousMoment h)
    ((chartPhiEquiv z (m * q)).symm_apply_apply (modeFormProduct m q u))

#assert_trust kernel modeFormProduct
#assert_trust kernel modeFormProduct_eq_sum
#assert_trust kernel hankel_multilinear_pairing
#assert_trust kernel chartPhi_modeFormProduct
#assert_trust kernel chart_hankel_multilinear
#print axioms chart_hankel_multilinear

end
end NLA.Proofs.TR14
