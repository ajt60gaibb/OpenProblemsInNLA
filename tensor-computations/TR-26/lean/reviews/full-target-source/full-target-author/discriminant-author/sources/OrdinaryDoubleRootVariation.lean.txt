import NLA.Proofs.TR26.FixedDiscriminantVariation

/-! The first variation of the actual fixed-degree binary discriminant at an
ordinary double root is a nonzero multiple of evaluation at that root. Every
zero-evaluation tangent direction is realized by a genuine double-root family. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR26.BinaryDiscriminant
open Polynomial

theorem polynomial_value_expansion (P : Polynomial ℂ) (r : ℂ) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ P.natDegree-1 ∧ P=C (P.eval r)+(X-C r)*Q := by
  let T := Polynomial.taylor r P
  have hh := Polynomial.X_mul_divX_add T
  have he : T=C (T.coeff 0)+X*T.divX := by linear_combination -hh
  refine ⟨Polynomial.taylor (-r) T.divX,?_,?_⟩
  · simp only [Polynomial.natDegree_taylor,Polynomial.natDegree_divX_eq_natDegree_tsub_one,T]
    omega
  · have h := congrArg (Polynomial.taylor (-r)) he
    have hX : (X : Polynomial ℂ)+C (-r)=X-C r := by simp [sub_eq_add_neg]
    simpa only [map_add,Polynomial.taylor_mul,Polynomial.taylor_C,Polynomial.taylor_X,T,
      Polynomial.taylor_taylor,neg_add_cancel,Polynomial.taylor_zero,Polynomial.taylor_coeff_zero,
      hX] using h

theorem polynomial_firstJet_expansion (P : Polynomial ℂ) (r : ℂ) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ P.natDegree-2 ∧
      P=C (P.eval r)+C (P.derivative.eval r)*(X-C r)+(X-C r)^2*Q := by
  let T := Polynomial.taylor r P
  have h0 := Polynomial.X_mul_divX_add T
  have h1 := Polynomial.X_mul_divX_add T.divX
  simp only [Polynomial.coeff_divX] at h1
  have he : T=C (T.coeff 0)+C (T.coeff 1)*X+X^2*T.divX.divX := by
    linear_combination -h0-X*h1
  refine ⟨Polynomial.taylor (-r) T.divX.divX,?_,?_⟩
  · simp only [Polynomial.natDegree_taylor,Polynomial.natDegree_divX_eq_natDegree_tsub_one,T]
    omega
  · have h := congrArg (Polynomial.taylor (-r)) he
    have hX : (X : Polynomial ℂ)+C (-r)=X-C r := by simp [sub_eq_add_neg]
    simpa only [map_add,Polynomial.taylor_mul,Polynomial.taylor_pow,Polynomial.taylor_C,
      Polynomial.taylor_X,T,Polynomial.taylor_taylor,neg_add_cancel,Polynomial.taylor_zero,
      Polynomial.taylor_coeff_zero,Polynomial.taylor_coeff_one,hX] using h

theorem fixedDiscriminantDifferential_zero_of_eval_zero {k : ℕ} (hk : 2 ≤ k)
    (r : ℂ) (S V : Polynomial ℂ) (hS : S.natDegree ≤ k-2) (hV : V.natDegree ≤ k)
    (hr : S.eval r ≠ 0) (hVr : V.eval r=0) :
    fixedDiscriminantDifferential k ((X-C r)^2*S) V=0 := by
  obtain ⟨Q,hQ,hSq⟩ := polynomial_value_expansion S r
  obtain ⟨U0,hU0,hVu⟩ := polynomial_firstJet_expansion V r
  let α : ℂ := -(V.derivative.eval r)/(2*S.eval r)
  let U : Polynomial ℂ := U0+C (2*α)*Q
  have hα : V.derivative.eval r+(2*α)*S.eval r=0 := by
    dsimp [α]
    field_simp [hr]
    ring
  have hC : C (V.derivative.eval r)+C (2*α)*C (S.eval r)=(0:Polynomial ℂ) := by
    rw [← map_mul,← map_add,hα,map_zero]
  have hU : U.natDegree ≤ k-2 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · omega
    · exact (natDegree_C_mul_le _ _).trans (by omega)
  have hVel : V=movingDoubleRootVelocity r α S U := by
    rw [hVu,hSq]
    rw [hVr,map_zero,zero_add]
    dsimp [movingDoubleRootVelocity,U]
    linear_combination (X-C r)*hC
  rw [hVel]
  exact fixedDiscriminantDifferential_moving_root_zero hk r α S U hS hU

theorem fixedDiscriminantDifferential_proportional_eval {k : ℕ} (hk : 2 ≤ k)
    (r : ℂ) (S V : Polynomial ℂ) (hS : S.natDegree ≤ k-2) (hV : V.natDegree ≤ k)
    (hr : S.eval r ≠ 0) :
    fixedDiscriminantDifferential k ((X-C r)^2*S) V =
      (V.eval r/S.eval r)*fixedDiscriminantDifferential k ((X-C r)^2*S) S := by
  let c := V.eval r/S.eval r
  have hdeg : (V-C c*S).natDegree ≤ k :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le hV ((natDegree_C_mul_le _ _).trans (by omega)))
  have hz : (V-C c*S).eval r=0 := by
    simp only [eval_sub,eval_mul,eval_C,c]
    rw [div_mul_cancel₀ _ hr,sub_self]
  have hh := fixedDiscriminantDifferential_zero_of_eval_zero hk r S (V-C c*S) hS hdeg hr hz
  have hsmul : C c*S=c • S := (Polynomial.smul_eq_C_mul c (p := S)).symm
  rw [map_sub,hsmul,map_smul,smul_eq_mul,sub_eq_zero] at hh
  exact hh

theorem fixedDiscriminantDifferential_split_direction (r : ℂ) (S : Polynomial ℂ)
    (hS : 0 < S.natDegree) :
    fixedDiscriminantDifferential (2+S.natDegree) ((X-C r)^2*S) S =
      doubleRootSplitScale S * S.eval r^4 := by
  have h1 := hasDerivAt_fixedDiscriminant_line (2+S.natDegree) ((X-C r)^2*S) S
  have hfun : (fun ε => MvPolynomial.eval
      (Polynomial.toFn (2+S.natDegree+1) ((X-C r)^2*S+C ε*S))
      (fixedDiscriminant (2+S.natDegree))) =
      (fun ε => MvPolynomial.eval
        (Polynomial.toFn (2+S.natDegree+1) (quadraticSplit r ε*S))
        (fixedDiscriminant (2+S.natDegree))) := by
    funext ε
    congr 2
    unfold quadraticSplit
    ring
  rw [hfun] at h1
  exact h1.unique (hasDerivAt_fixedDiscriminant_double_root_split r S hS)

theorem fixedDiscriminantDifferential_ordinary_double_root (r : ℂ) (S V : Polynomial ℂ)
    (hS : 0 < S.natDegree) (hV : V.natDegree ≤ 2+S.natDegree) (hr : S.eval r ≠ 0) :
    fixedDiscriminantDifferential (2+S.natDegree) ((X-C r)^2*S) V =
      doubleRootSplitScale S * S.eval r^3 * V.eval r := by
  rw [fixedDiscriminantDifferential_proportional_eval (by omega) r S V (by omega) hV hr,
    fixedDiscriminantDifferential_split_direction r S hS]
  field_simp [hr]

theorem hasDerivAt_fixedDiscriminant_ordinary_double_root (r : ℂ) (S V : Polynomial ℂ)
    (hS : 0 < S.natDegree) (hV : V.natDegree ≤ 2+S.natDegree) (hr : S.eval r ≠ 0) :
    HasDerivAt
      (fun ε => MvPolynomial.eval
        (Polynomial.toFn (2+S.natDegree+1) ((X-C r)^2*S+C ε*V))
        (fixedDiscriminant (2+S.natDegree)))
      (doubleRootSplitScale S * S.eval r^3 * V.eval r) 0 := by
  rw [← fixedDiscriminantDifferential_ordinary_double_root r S V hS hV hr]
  exact hasDerivAt_fixedDiscriminant_line _ _ _

theorem fixedDiscriminant_ordinary_double_root_derivative_ne_zero
    (r : ℂ) (S V : Polynomial ℂ) (hS : 0 < S.natDegree) (hsep : S.Separable)
    (hr : S.eval r ≠ 0) (hVr : V.eval r ≠ 0) :
    doubleRootSplitScale S * S.eval r^3 * V.eval r ≠ 0 := by
  have hscale : doubleRootSplitScale S ≠ 0 := by
    intro hz
    exact double_root_split_derivative_ne_zero r S hS hsep hr (by rw [hz,zero_mul])
  exact mul_ne_zero (mul_ne_zero hscale (pow_ne_zero _ hr)) hVr

#assert_trust kernel fixedDiscriminantDifferential_zero_of_eval_zero
#assert_trust kernel fixedDiscriminantDifferential_proportional_eval
#assert_trust kernel fixedDiscriminantDifferential_ordinary_double_root
#assert_trust kernel hasDerivAt_fixedDiscriminant_ordinary_double_root
#assert_trust kernel fixedDiscriminant_ordinary_double_root_derivative_ne_zero
#print axioms hasDerivAt_fixedDiscriminant_ordinary_double_root
end NLA.Proofs.TR26.BinaryDiscriminant
