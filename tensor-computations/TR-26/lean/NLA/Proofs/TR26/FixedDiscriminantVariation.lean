import NLA.Proofs.TR26.DoubleRootSplitVariation
import NLA.Proofs.TR26.AnalyticConormal
import Mathlib.Algebra.Polynomial.Taylor

/-! The genuine coefficient differential of the fixed Sylvester determinant.
Its vanishing on tangent directions is proved by an actual family of binary
forms retaining a double root. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR26.BinaryDiscriminant
open Polynomial

def fixedDiscriminantDifferential (k : ℕ) (F : Polynomial ℂ) : Polynomial ℂ →ₗ[ℂ] ℂ where
  toFun V := ∑ i : Fin (k+1),
    MvPolynomial.eval (Polynomial.toFn (k+1) F) (MvPolynomial.pderiv i (fixedDiscriminant k))*
      V.coeff i.val
  map_add' V W := by simp [coeff_add,mul_add,Finset.sum_add_distrib]
  map_smul' c V := by
    simp only [Polynomial.smul_eq_C_mul,coeff_C_mul,smul_eq_mul,RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem hasDerivAt_fixedDiscriminant_polynomial_path (k : ℕ)
    (P : ℂ → Polynomial ℂ) (V : Polynomial ℂ)
    (hP : ∀ i : Fin (k+1), HasDerivAt (fun ε => (P ε).coeff i.val) (V.coeff i.val) 0) :
    HasDerivAt (fun ε => MvPolynomial.eval (Polynomial.toFn (k+1) (P ε)) (fixedDiscriminant k))
      (fixedDiscriminantDifferential k (P 0) V) 0 := by
  have hh := hasDerivAt_eval_curve (fixedDiscriminant k)
    (fun ε => Polynomial.toFn (k+1) (P ε)) (Polynomial.toFn (k+1) V) 0 hP
  exact hh

theorem hasDerivAt_fixedDiscriminant_line (k : ℕ) (F V : Polynomial ℂ) :
    HasDerivAt
      (fun ε => MvPolynomial.eval (Polynomial.toFn (k+1) (F+C ε*V)) (fixedDiscriminant k))
      (fixedDiscriminantDifferential k F V) 0 := by
  have hh := hasDerivAt_fixedDiscriminant_polynomial_path k (fun ε => F+C ε*V) V (by
    intro i
    convert! (hasDerivAt_const (0:ℂ) (F.coeff i.val)).add
        ((hasDerivAt_id (0:ℂ)).mul_const (V.coeff i.val)) using 1 <;>
      simp [funext_iff,coeff_add,coeff_C_mul])
  simpa only [map_zero,zero_mul,add_zero] using hh

theorem fixedDiscriminant_zero_of_affine_double_root {k : ℕ} (hk : 2 ≤ k)
    (F : Polynomial ℂ) (hF : F.natDegree ≤ k) (r : ℂ)
    (hr : F.eval r=0) (hr' : F.derivative.eval r=0) :
    MvPolynomial.eval (Polynomial.toFn (k+1) F) (fixedDiscriminant k)=0 := by
  have hrec : Polynomial.ofFn (k+1) (Polynomial.toFn (k+1) F)=F :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  apply multiple_projective_root_vanishes hk
  refine ⟨1,r,Or.inl one_ne_zero,?_,?_⟩
  · rw [homogeneousEval_at_one,partialA_ofFn_eq_euler,hrec]
    simp [hr,hr']
  · rw [homogeneousEval_at_one,partialB_ofFn_eq_derivative,hrec]
    exact hr'

def movingDoubleRoot (r α : ℂ) (S U : Polynomial ℂ) (ε : ℂ) : Polynomial ℂ :=
  (X-C (r+ε*α))^2*(S+C ε*U)

def movingDoubleRootVelocity (r α : ℂ) (S U : Polynomial ℂ) : Polynomial ℂ :=
  (X-C r)^2*U-C (2*α)*(X-C r)*S

theorem movingDoubleRoot_zero (r α : ℂ) (S U : Polynomial ℂ) :
    movingDoubleRoot r α S U 0=(X-C r)^2*S := by
  simp [movingDoubleRoot]

theorem movingDoubleRoot_expansion (r α : ℂ) (S U : Polynomial ℂ) (ε : ℂ) :
    movingDoubleRoot r α S U ε = (X-C r)^2*S+
      C ε*movingDoubleRootVelocity r α S U+
      C (ε^2)*(C (α^2)*S-C (2*α)*(X-C r)*U)+C (ε^3)*(C (α^2)*U) := by
  simp only [movingDoubleRoot,movingDoubleRootVelocity,map_add,map_mul,map_pow,map_ofNat]
  ring

theorem movingDoubleRoot_coeff_hasDerivAt (r α : ℂ) (S U : Polynomial ℂ) (n : ℕ) :
    HasDerivAt (fun ε => (movingDoubleRoot r α S U ε).coeff n)
      ((movingDoubleRootVelocity r α S U).coeff n) 0 := by
  have he (ε : ℂ) : (movingDoubleRoot r α S U ε).coeff n =
      ((X-C r)^2*S).coeff n+ε*(movingDoubleRootVelocity r α S U).coeff n+
      ε^2*(C (α^2)*S-C (2*α)*(X-C r)*U).coeff n+
      ε^3*(C (α^2)*U).coeff n := by
    rw [movingDoubleRoot_expansion]
    simp only [coeff_add,coeff_C_mul]
  have hh := ((hasDerivAt_const (0:ℂ) (((X-C r)^2*S).coeff n)).add
    ((hasDerivAt_id (0:ℂ)).mul_const ((movingDoubleRootVelocity r α S U).coeff n))).add
    (((hasDerivAt_id (0:ℂ)).pow 2).mul_const
      ((C (α^2)*S-C (2*α)*(X-C r)*U).coeff n))
  have hh' := hh.add (((hasDerivAt_id (0:ℂ)).pow 3).mul_const ((C (α^2)*U).coeff n))
  convert! hh' using 1
  · ext ε
    exact he ε
  · simp

theorem movingDoubleRoot_natDegree_le {k : ℕ} (hk : 2 ≤ k)
    (r α ε : ℂ) (S U : Polynomial ℂ) (hS : S.natDegree ≤ k-2) (hU : U.natDegree ≤ k-2) :
    (movingDoubleRoot r α S U ε).natDegree ≤ k := by
  have htail : (S+C ε*U).natDegree ≤ k-2 :=
    Polynomial.natDegree_add_le_of_degree_le hS ((natDegree_C_mul_le _ _).trans hU)
  have hp : (((X-C (r+ε*α)) : Polynomial ℂ)^2).natDegree=2 := by
    rw [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one]
  have hh : (movingDoubleRoot r α S U ε).natDegree ≤ 2+(S+C ε*U).natDegree := by
    change (((X-C (r+ε*α)) : Polynomial ℂ)^2*(S+C ε*U)).natDegree ≤ _
    calc
      _ ≤ (((X-C (r+ε*α)) : Polynomial ℂ)^2).natDegree+(S+C ε*U).natDegree :=
        Polynomial.natDegree_mul_le
      _ = _ := by rw [hp]
  omega

theorem fixedDiscriminantDifferential_moving_root_zero {k : ℕ} (hk : 2 ≤ k)
    (r α : ℂ) (S U : Polynomial ℂ) (hS : S.natDegree ≤ k-2) (hU : U.natDegree ≤ k-2) :
    fixedDiscriminantDifferential k ((X-C r)^2*S) (movingDoubleRootVelocity r α S U)=0 := by
  have hh := hasDerivAt_fixedDiscriminant_polynomial_path k (movingDoubleRoot r α S U)
    (movingDoubleRootVelocity r α S U) (fun i => movingDoubleRoot_coeff_hasDerivAt r α S U i.val)
  rw [movingDoubleRoot_zero] at hh
  have hz (ε : ℂ) : MvPolynomial.eval
      (Polynomial.toFn (k+1) (movingDoubleRoot r α S U ε)) (fixedDiscriminant k)=0 := by
    apply fixedDiscriminant_zero_of_affine_double_root hk _
      (movingDoubleRoot_natDegree_le hk r α ε S U hS hU) (r+ε*α)
    · simp [movingDoubleRoot]
    · simp [movingDoubleRoot,Polynomial.derivative_pow]
  have hh0 : HasDerivAt (fun ε => MvPolynomial.eval
      (Polynomial.toFn (k+1) (movingDoubleRoot r α S U ε)) (fixedDiscriminant k)) 0 0 := by
    simpa only [hz] using hasDerivAt_const (0:ℂ) (0:ℂ)
  exact hh.unique hh0

#assert_trust kernel hasDerivAt_fixedDiscriminant_line
#assert_trust kernel fixedDiscriminant_zero_of_affine_double_root
#assert_trust kernel fixedDiscriminantDifferential_moving_root_zero
#print axioms fixedDiscriminantDifferential_moving_root_zero
end NLA.Proofs.TR26.BinaryDiscriminant
