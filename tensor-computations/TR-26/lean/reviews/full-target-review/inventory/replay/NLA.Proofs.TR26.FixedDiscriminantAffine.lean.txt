import NLA.Proofs.TR26.FixedDiscriminantResultant
import NLA.Proofs.TR26.Wronskian

/-! The exact nonzero normalization of the actual fixed binary discriminant
on the full-degree affine chart. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR26.BinaryDiscriminant
open Polynomial

theorem dehomogenize_binaryFromCoefficients (k : ℕ) (c : Fin (k+1) → ℂ) :
    binaryDehomogenizeOver ℂ (binaryFromCoefficients k c) = Polynomial.ofFn (k+1) c := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp [binaryFromCoefficients,binaryDehomogenizeOver,Polynomial.C_mul_X_pow_eq_monomial]

theorem partialB_ofFn_eq_derivative (k : ℕ) (c : Fin (k+1) → ℂ) :
    Polynomial.ofFn k (partialBCoeff k c) = (Polynomial.ofFn (k+1) c).derivative := by
  rw [← dehomogenize_binaryFromCoefficients,← binaryDehomogenize_pderiv_b,
    binaryFromCoefficients_partialB,Polynomial.ofFn_eq_sum_monomial]
  simp [binaryDehomogenizeOver,Polynomial.C_mul_X_pow_eq_monomial]

theorem partialA_ofFn_eq_euler (k : ℕ) (c : Fin (k+1) → ℂ) :
    Polynomial.ofFn k (partialACoeff k c) =
      C (k : ℂ) * Polynomial.ofFn (k+1) c - X*(Polynomial.ofFn (k+1) c).derivative := by
  rw [← dehomogenize_binaryFromCoefficients,← binaryDehomogenize_pderiv_a _
    (binaryFromCoefficients_homogeneous k c),binaryFromCoefficients_partialA,
    Polynomial.ofFn_eq_sum_monomial]
  simp [binaryDehomogenizeOver,Polynomial.C_mul_X_pow_eq_monomial]

theorem eval_fixedDiscriminant_eq_resultant_euler {k : ℕ} (hk : 0 < k)
    (c : Fin (k+1) → ℂ) :
    MvPolynomial.eval c (fixedDiscriminant k) =
      Polynomial.resultant (Polynomial.ofFn (k+1) c).derivative
        (C (k : ℂ)*Polynomial.ofFn (k+1) c-X*(Polynomial.ofFn (k+1) c).derivative)
        (k-1) (k-1) := by
  rw [eval_fixedDiscriminant_resultant hk,partialA_ofFn_eq_euler,partialB_ofFn_eq_derivative]

theorem resultant_euler_eq_scaled_discr (k : ℕ) (hk : 2 ≤ k)
    (f : Polynomial ℂ) (hf : f.natDegree = k) :
    Polynomial.resultant f.derivative (C (k : ℂ)*f-X*f.derivative) (k-1) (k-1) =
      (-1 : ℂ)^(k*(k-1)/2) * (k : ℂ)^(k-2) * f.discr := by
  let A := C (k : ℂ)*f-X*f.derivative
  have hf0 : f ≠ 0 := by intro h; rw [h,natDegree_zero] at hf; omega
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hld : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  have hderdeg : f.derivative.natDegree = k-1 := by rw [natDegree_derivative,hf]
  have hAdeg : A.natDegree ≤ k-1 := by
    have hA : A = Polynomial.ofFn k (fun i => A.coeff i.val) := by
      apply Polynomial.ext
      intro n
      by_cases hn : n < k
      · simp [hn]
      · rw [ofFn_coeff_eq_zero_of_ge _ (by omega)]
        dsimp [A]
        rw [coeff_sub,coeff_C_mul]
        have hn1 : n-1+1=n := by omega
        have hx : (X*f.derivative).coeff n = f.derivative.coeff (n-1) := by
          conv_lhs => rw [← hn1]
          rw [coeff_X_mul]
        rw [hx,coeff_derivative,hn1]
        have hc : ((n-1 : ℕ) : ℂ)+1=(n:ℂ) := by exact_mod_cast hn1
        rw [hc]
        by_cases hnk : n=k
        · subst n
          ring
        · have hkn : k < n := by omega
          rw [coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < n)]
          ring
    rw [hA]
    exact Nat.le_sub_one_of_lt (ofFn_natDegree_lt (by omega) _)
  have hext := Polynomial.resultant_add_right_deg f.derivative A (k-1) (k-1) 1 hAdeg
  have hsucc : k-1+1=k := by omega
  rw [hsucc,pow_one] at hext
  have hlc : f.derivative.coeff (k-1) = f.leadingCoeff*(k:ℂ) := by
    rw [← hderdeg,coeff_natDegree,leadingCoeff_derivative,hf]
  rw [hlc] at hext
  have hadd := Polynomial.resultant_add_mul_right f.derivative A X (k-1) k
    (by simp; omega) (by omega)
  have heuler : A+f.derivative*X=C (k:ℂ)*f := by dsimp [A]; ring
  rw [heuler,Polynomial.resultant_C_mul_right] at hadd
  have hcomm : Polynomial.resultant f.derivative f (k-1) k =
      Polynomial.resultant f f.derivative k (k-1) := by
    rw [Polynomial.resultant_comm]
    have heven : Even ((k-1)*k) := by
      have h := Nat.even_mul_pred_self k
      simpa [mul_comm] using h
    rw [heven.neg_one_pow,one_mul]
  rw [hcomm] at hadd
  have hres := Polynomial.resultant_deriv (f := f) (by rw [← natDegree_pos_iff_degree_pos,hf]; omega)
  rw [hf] at hres
  rw [hres] at hadd
  have heq : f.leadingCoeff*(k:ℂ) * Polynomial.resultant f.derivative A (k-1) (k-1) =
      (k:ℂ)^(k-1) * ((-1:ℂ)^(k*(k-1)/2)*f.leadingCoeff*f.discr) := hext.symm.trans hadd.symm
  have hp : (k:ℂ)^(k-1)=(k:ℂ)*(k:ℂ)^(k-2) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hp] at heq
  apply mul_left_cancel₀ (mul_ne_zero hld hkC)
  calc
    _ = (k:ℂ)*(k:ℂ)^(k-2)*((-1:ℂ)^(k*(k-1)/2)*f.leadingCoeff*f.discr) := heq
    _ = _ := by ring

theorem eval_fixedDiscriminant_eq_scaled_discr {k : ℕ} (hk : 2 ≤ k)
    (c : Fin (k+1) → ℂ) (hc : (Polynomial.ofFn (k+1) c).natDegree = k) :
    MvPolynomial.eval c (fixedDiscriminant k) =
      (-1 : ℂ)^(k*(k-1)/2) * (k : ℂ)^(k-2) * (Polynomial.ofFn (k+1) c).discr := by
  rw [eval_fixedDiscriminant_eq_resultant_euler (by omega)]
  exact resultant_euler_eq_scaled_discr k hk _ hc

#assert_trust kernel partialB_ofFn_eq_derivative
#assert_trust kernel partialA_ofFn_eq_euler
#assert_trust kernel resultant_euler_eq_scaled_discr
#assert_trust kernel eval_fixedDiscriminant_eq_scaled_discr
#print axioms eval_fixedDiscriminant_eq_scaled_discr
end NLA.Proofs.TR26.BinaryDiscriminant
