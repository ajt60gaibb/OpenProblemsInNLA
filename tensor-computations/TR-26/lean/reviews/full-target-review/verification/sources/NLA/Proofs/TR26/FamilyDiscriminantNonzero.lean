import NLA.Proofs.TR26.FamilyDiscriminantEvaluation
import NLA.Proofs.TR26.BinaryScaling
import NLA.Proofs.TR26.WronskianPencil
import Mathlib.Algebra.Polynomial.OfFn

/-! Nonvanishing of the actual fixed-denominator family discriminant. A proved
finite-exception pencil gives a separable affine Wronskian of the full fixed
degree; the projective infinity chart is checked explicitly. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem binaryDehomogenize_eq_ofFn {k : ℕ} (P : BinaryForm ℂ) (hP : P.IsHomogeneous k) :
    binaryDehomogenizeOver ℂ P = Polynomial.ofFn (k + 1) (binaryCoeff k P) := by
  classical
  conv_lhs => rw [binary_homogeneous_reconstruct P hP]
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [binaryDehomogenizeOver, map_sum, map_mul, map_pow, eval₂Hom_C, eval₂Hom_X',
    Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one,
    Polynomial.C_mul_X_pow_eq_monomial]

theorem binary_top_value {k : ℕ} (P : BinaryForm ℂ) (hP : P.IsHomogeneous k) :
    binaryEval P 0 1 = binaryCoeff k P (Fin.last k) := by
  classical
  conv_lhs => rw [binary_homogeneous_reconstruct P hP]
  simp only [binaryEvalOver, map_sum, map_mul, map_pow, eval_C, eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one]
  rw [Finset.sum_eq_single (Fin.last k)]
  · simp
  · intro i _ hi
    have hival : i.val < k := by
      have hle : i.val ≤ k := Nat.le_of_lt_succ i.isLt
      have hne : i.val ≠ k := by intro heq; apply hi; exact Fin.ext heq
      omega
    simp [zero_pow (by omega : k - i.val ≠ 0)]
  · simp

theorem no_projective_multiple_root_of_separable_full_affine {k : ℕ} (hk : 0 < k)
    (P : BinaryForm ℂ) (hP : P.IsHomogeneous k)
    (hsep : (binaryDehomogenizeOver ℂ P).Separable)
    (hdeg : (binaryDehomogenizeOver ℂ P).natDegree = k) :
    ¬ ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧
      binaryEval (pderiv 0 P) a b = 0 ∧ binaryEval (pderiv 1 P) a b = 0 := by
  rintro ⟨a, b, hab, ha, hb⟩
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have heuler := binary_euler_eval P hP a b
  rw [ha, hb, mul_zero, mul_zero, zero_add] at heuler
  have hzero : binaryEval P a b = 0 := (mul_eq_zero.mp heuler.symm).resolve_left hkC
  by_cases ha0 : a = 0
  · have hbne : b ≠ 0 := hab.resolve_left (not_not.mpr ha0)
    rw [ha0] at hzero
    have hscale := binaryEval_homogeneous_smul k P hP 0 1 b
    simp only [mul_zero, mul_one] at hscale
    rw [hscale] at hzero
    have htopzero : binaryEval P 0 1 = 0 := (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hbne)
    have htop : (binaryDehomogenizeOver ℂ P).coeff k = binaryEval P 0 1 := by
      rw [binaryDehomogenize_eq_ofFn P hP, Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega),
        binary_top_value P hP]
      rfl
    have hqne : binaryDehomogenizeOver ℂ P ≠ 0 := by
      intro hz
      rw [hz, Polynomial.natDegree_zero] at hdeg
      omega
    have hc : (binaryDehomogenizeOver ℂ P).coeff k ≠ 0 := by
      rw [← hdeg, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hqne
    exact hc (htop.trans htopzero)
  · have hP1 : binaryEval P 1 (b / a) = 0 := by
      rw [binaryEval_affine_ratio k P hP a b ha0] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ ha0)
    have hPb1 : binaryEval (pderiv 1 P) 1 (b / a) = 0 := by
      rw [binaryEval_affine_ratio (k - 1) (pderiv 1 P) (hP.pderiv (i := 1)) a b ha0] at hb
      exact (mul_eq_zero.mp hb).resolve_left (pow_ne_zero _ ha0)
    have hq : (binaryDehomogenizeOver ℂ P).eval (b / a) = 0 :=
      (binaryDehomogenize_eval P (b / a)).trans hP1
    have hqd : (binaryDehomogenizeOver ℂ P).derivative.eval (b / a) = 0 := by
      rw [← binaryDehomogenize_pderiv_b]
      exact (binaryDehomogenize_eval (pderiv 1 P) (b / a)).trans hPb1
    exact (hsep.aeval_derivative_ne_zero hq) hqd

theorem wronskianFamilyDiscriminant_ne_zero {d : ℕ} (hd : 2 ≤ d) :
    wronskianFamilyDiscriminant d ≠ 0 := by
  obtain ⟨H, hsep, hdeg⟩ := exists_separable_full_degree_affineWronskian hd
  intro hz
  have heval : MvPolynomial.eval H (wronskianFamilyDiscriminant d) = 0 := by rw [hz, map_zero]
  have hroot := (eval_wronskianFamilyDiscriminant_eq_zero_iff (by omega : 1 ≤ d) H).mp heval
  apply no_projective_multiple_root_of_separable_full_affine (by omega : 0 < 4 * d - 2)
    (binaryWronskian H) (binaryWronskianOver_homogeneous H) _ _ hroot
  · simpa only [binaryDehomogenize_wronskian (by omega : 0 < d)] using hsep
  · simpa only [binaryDehomogenize_wronskian (by omega : 0 < d)] using hdeg

theorem wronskianFamilyDiscriminant_totalDegree {d : ℕ} (hd : 2 ≤ d) :
    (wronskianFamilyDiscriminant d).totalDegree = 8 * d - 6 :=
  (wronskianFamilyDiscriminant_homogeneous (by omega)).totalDegree
    (wronskianFamilyDiscriminant_ne_zero hd)

#assert_trust kernel no_projective_multiple_root_of_separable_full_affine
#assert_trust kernel wronskianFamilyDiscriminant_ne_zero
#assert_trust kernel wronskianFamilyDiscriminant_totalDegree
#print axioms wronskianFamilyDiscriminant_ne_zero
#print axioms wronskianFamilyDiscriminant_totalDegree
end NLA.Proofs.TR26
