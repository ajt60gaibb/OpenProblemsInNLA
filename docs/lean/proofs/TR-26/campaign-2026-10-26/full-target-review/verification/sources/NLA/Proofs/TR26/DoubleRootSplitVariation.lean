import NLA.Proofs.TR26.DiscriminantProduct

/-! An actual transverse one-parameter splitting of a unique ordinary double
root. This computes the derivative of the fixed-degree Sylvester determinant
itself, including its nonzero scalar normalization. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR26.BinaryDiscriminant
open Polynomial

def quadraticSplit (r ε : ℂ) : Polynomial ℂ := (X-C r)^2+C ε

theorem quadraticSplit_degree (r ε : ℂ) : (quadraticSplit r ε).natDegree=2 := by
  unfold quadraticSplit
  rw [natDegree_add_eq_left_of_natDegree_lt (by simp [natDegree_pow])]
  simp [natDegree_pow]

theorem quadraticSplit_discr (r ε : ℂ) : (quadraticSplit r ε).discr = -4*ε := by
  have hq0 : quadraticSplit r ε ≠ 0 := by
    intro hz
    have hd := quadraticSplit_degree r ε
    rw [hz,natDegree_zero] at hd
    omega
  have hd : (quadraticSplit r ε).degree=2 := by
    rw [degree_eq_natDegree hq0,quadraticSplit_degree]
    rfl
  rw [Polynomial.discr_of_degree_eq_two hd]
  simp only [quadraticSplit,pow_two,sub_mul,mul_sub,coeff_add,coeff_sub,
    coeff_X_mul,coeff_C_mul,coeff_C,coeff_X,coeff_mul_X]
  norm_num
  ring

def quadraticResultantPolynomial (r : ℂ) (S : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.resultant
    (((X-C (C r))^2+C (X : Polynomial ℂ)) : Polynomial (Polynomial ℂ))
    (S.map Polynomial.C) 2 S.natDegree

theorem quadraticResultantPolynomial_eval (r ε : ℂ) (S : Polynomial ℂ) :
    (quadraticResultantPolynomial r S).eval ε =
      Polynomial.resultant (quadraticSplit r ε) S 2 S.natDegree := by
  change (Polynomial.evalRingHom ε) (quadraticResultantPolynomial r S) = _
  unfold quadraticResultantPolynomial
  rw [← Polynomial.resultant_map_map]
  have hm : (S.map Polynomial.C).map (Polynomial.evalRingHom ε)=S := by
    have hcomp : (Polynomial.evalRingHom ε).comp Polynomial.C=RingHom.id ℂ := by
      ext z
      simp
    rw [Polynomial.map_map,hcomp,Polynomial.map_id]
  rw [hm]
  congr 1
  simp [quadraticSplit]

def binaryDiscriminantScale (k : ℕ) : ℂ := discriminantSign k*(k:ℂ)^(k-2)

def discriminantProductScale (m n : ℕ) : ℂ :=
  discriminantSign (m+n)*discriminantSign m*discriminantSign n*(-1:ℂ)^(m*n)

def doubleRootSplitScale (S : Polynomial ℂ) : ℂ :=
  binaryDiscriminantScale (2+S.natDegree)*discriminantProductScale 2 S.natDegree*
    (-4)*S.discr

theorem binaryDiscriminantScale_ne_zero {k : ℕ} (hk : 2 ≤ k) : binaryDiscriminantScale k ≠ 0 := by
  unfold binaryDiscriminantScale discriminantSign
  exact mul_ne_zero (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ (by exact_mod_cast (by omega : k ≠ 0)))

theorem discriminantProductScale_ne_zero (m n : ℕ) : discriminantProductScale m n ≠ 0 := by
  unfold discriminantProductScale discriminantSign
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ (by norm_num))) (pow_ne_zero _ (by norm_num)))
    (pow_ne_zero _ (by norm_num))

theorem fixedDiscriminant_quadraticSplit_product (r ε : ℂ) (S : Polynomial ℂ)
    (hS : 0 < S.natDegree) :
    MvPolynomial.eval (Polynomial.toFn (2+S.natDegree+1) (quadraticSplit r ε*S))
      (fixedDiscriminant (2+S.natDegree)) =
      doubleRootSplitScale S * ε * (quadraticResultantPolynomial r S).eval ε ^ 2 := by
  have hS0 : S ≠ 0 := by intro h; simp [h] at hS
  have hq0 : quadraticSplit r ε ≠ 0 := by
    intro hz
    have hh := quadraticSplit_degree r ε
    rw [hz,natDegree_zero] at hh
    omega
  have hdeg : (quadraticSplit r ε*S).natDegree=2+S.natDegree := by
    rw [natDegree_mul hq0 hS0,quadraticSplit_degree]
  rw [eval_fixedDiscriminant_eq_scaled_discr (by omega : 2 ≤ 2+S.natDegree) _ (by
    rw [Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)]
    exact hdeg)]
  rw [Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega),
    discr_mul_with_sign _ _ (by rw [quadraticSplit_degree]; omega) hS,
    quadraticSplit_degree,quadraticSplit_discr,quadraticResultantPolynomial_eval]
  unfold doubleRootSplitScale binaryDiscriminantScale discriminantProductScale discriminantSign
  ring

theorem hasDerivAt_fixedDiscriminant_double_root_split (r : ℂ) (S : Polynomial ℂ)
    (hS : 0 < S.natDegree) :
    HasDerivAt
      (fun ε => MvPolynomial.eval
        (Polynomial.toFn (2+S.natDegree+1) (quadraticSplit r ε*S))
        (fixedDiscriminant (2+S.natDegree)))
      (doubleRootSplitScale S * S.eval r ^ 4) 0 := by
  have hR := (quadraticResultantPolynomial r S).hasDerivAt 0
  have hval : (quadraticResultantPolynomial r S).eval 0 = S.eval r ^ 2 := by
    rw [quadraticResultantPolynomial_eval]
    have hq : quadraticSplit r 0 = (X-C r)^2 := by
      unfold quadraticSplit
      rw [map_zero,add_zero]
    rw [hq]
    exact resultant_X_sub_C_pow_left r S 2 S.natDegree le_rfl
  have hh := ((hasDerivAt_id (0:ℂ)).mul (hR.pow 2)).const_mul (doubleRootSplitScale S)
  convert! hh using 1
  · ext ε
    simpa only [Pi.mul_apply,Pi.pow_apply,id_eq,mul_assoc] using
      fixedDiscriminant_quadraticSplit_product r ε S hS
  · simp only [Pi.pow_apply,id_eq,mul_zero,add_zero,one_mul]
    rw [hval]
    ring

theorem double_root_split_derivative_ne_zero (r : ℂ) (S : Polynomial ℂ)
    (hS : 0 < S.natDegree) (hsep : S.Separable) (hr : S.eval r ≠ 0) :
    doubleRootSplitScale S * S.eval r ^ 4 ≠ 0 := by
  unfold doubleRootSplitScale
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (binaryDiscriminantScale_ne_zero (by omega)) (discriminantProductScale_ne_zero _ _))
      (by norm_num)) (discr_ne_zero_of_separable S hS hsep)) (pow_ne_zero _ hr)

#assert_trust kernel fixedDiscriminant_quadraticSplit_product
#assert_trust kernel hasDerivAt_fixedDiscriminant_double_root_split
#assert_trust kernel double_root_split_derivative_ne_zero
#print axioms hasDerivAt_fixedDiscriminant_double_root_split
end NLA.Proofs.TR26.BinaryDiscriminant
