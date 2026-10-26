import NLA.Proofs.TR26.WronskianBinaryLinear
import NLA.Proofs.TR26.WronskianCharts
import NLA.Proofs.TR26.FamilyDiscriminantNonzero

/-! The second actual projective chart, including infinity. Fixed binary degree
is retained; no degree-changing polynomial reversal is used. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Topology
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

/-- Dehomogenization in the chart where the second coordinate is nonzero. -/
def binaryReverseDehomogenizeOver (R : Type*) [CommSemiring R] :
    BinaryForm R →+* Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X,1]

theorem binaryReverseDehomogenize_eval (P : BinaryForm ℂ) (t : ℂ) :
    (binaryReverseDehomogenizeOver ℂ P).eval t = binaryEval P t 1 := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [binaryReverseDehomogenizeOver,binaryEvalOver]
  | add P Q hP hQ =>
    simp only [map_add,Polynomial.eval_add,binaryEvalOver] at *
    rw [hP,hQ]
  | mul_X P i hP =>
    simp only [map_mul,Polynomial.eval_mul,binaryEvalOver] at *
    rw [hP]
    fin_cases i <;> simp [binaryReverseDehomogenizeOver]

theorem binaryReverseDehomogenize_pderiv_a {R : Type*} [CommSemiring R]
    (P : BinaryForm R) :
    binaryReverseDehomogenizeOver R (MvPolynomial.pderiv 0 P) =
      (binaryReverseDehomogenizeOver R P).derivative := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [binaryReverseDehomogenizeOver]
  | add P Q hP hQ =>
    simp only [map_add,hP,hQ]
  | mul_X P i hP =>
    simp only [MvPolynomial.pderiv_mul,map_add,map_mul,Polynomial.derivative_mul,hP]
    fin_cases i <;> simp [binaryReverseDehomogenizeOver]

def reverseWronskian {d : ℕ} (H : Parameter d) : Polynomial ℂ :=
  binaryReverseDehomogenizeOver ℂ (binaryWronskian H)

def reverseDenominator (d : ℕ) : Polynomial ℂ :=
  binaryReverseDehomogenizeOver ℂ (binaryDenominator d)

def reverseWronskianLinear (d : ℕ) : Parameter d →ₗ[ℂ] Polynomial ℂ where
  toFun := reverseWronskian
  map_add' H K := by
    change binaryReverseDehomogenizeOver ℂ (binaryWronskianLinear d (H+K)) = _
    rw [map_add,map_add]
    rfl
  map_smul' c H := by
    change binaryReverseDehomogenizeOver ℂ (binaryWronskianLinear d (c • H)) =
      c • binaryReverseDehomogenizeOver ℂ (binaryWronskianLinear d H)
    rw [map_smul,MvPolynomial.smul_eq_C_mul,map_mul]
    simp [binaryReverseDehomogenizeOver,Polynomial.smul_eq_C_mul]

theorem reverseWronskianLinear_apply {d : ℕ} (H : Parameter d) :
    reverseWronskianLinear d H = reverseWronskian H := rfl

def reverseCriticalCoefficients (d : ℕ) (j : SymIndex d) : Polynomial ℂ :=
  reverseWronskian (Pi.single j 1)

theorem linearCriticalPolynomial_reverse {d : ℕ} (H : Parameter d) :
    linearCriticalPolynomial (reverseCriticalCoefficients d) H = reverseWronskian H := by
  classical
  have hrep : H = ∑ j : SymIndex d, H j • Pi.single j 1 := by
    ext j
    simp [Pi.single_apply]
  have hh := congrArg (reverseWronskianLinear d) hrep
  rw [map_sum] at hh
  simp only [map_smul,reverseWronskianLinear_apply] at hh
  simpa only [linearCriticalPolynomial,reverseCriticalCoefficients,
    Polynomial.smul_eq_C_mul] using hh.symm

theorem linearCriticalValue_reverse {d : ℕ} (t : ℂ) (H : Parameter d) :
    linearCriticalValue (reverseCriticalCoefficients d) t H =
      (reverseWronskian H).eval t := by
  rw [← linearCriticalPolynomial_eval,linearCriticalPolynomial_reverse]

theorem reverseWronskian_eval {d : ℕ} (H : Parameter d) (t : ℂ) :
    (reverseWronskian H).eval t = binaryEval (binaryWronskian H) t 1 :=
  binaryReverseDehomogenize_eval _ _

theorem reverseWronskian_derivative_eval {d : ℕ} (H : Parameter d) (t : ℂ) :
    (reverseWronskian H).derivative.eval t =
      binaryEval (MvPolynomial.pderiv 0 (binaryWronskian H)) t 1 := by
  rw [← binaryReverseDehomogenize_eval, binaryReverseDehomogenize_pderiv_a]
  rfl

theorem reverseDenominator_eval (d : ℕ) (t : ℂ) :
    (reverseDenominator d).eval t = denominator (veronese d t 1) := by
  rw [reverseDenominator,binaryReverseDehomogenize_eval,binaryDenominator_eval]

theorem reverseDenominator_ne_zero (d : ℕ) : reverseDenominator d ≠ 0 := by
  intro h
  have he := binaryReverseDehomogenize_eval (binaryDenominator d) 0
  change (reverseDenominator d).eval 0 = _ at he
  rw [h,Polynomial.eval_zero,binaryDenominator_eval_zero_one] at he
  exact zero_ne_one he

theorem exists_binaryWronskian_infinity_ne_zero {d : ℕ} (hd : 2 ≤ d) :
    ∃ H : Parameter d, binaryEval (binaryWronskian H) 0 1 ≠ 0 := by
  obtain ⟨H,_hsep,hdeg⟩ := exists_separable_full_degree_affineWronskian hd
  refine ⟨H,?_⟩
  have hhom := binaryWronskianOver_homogeneous H
  have htop : (affineWronskian H).coeff (4*d-2) =
      binaryEval (binaryWronskian H) 0 1 := by
    change (affineWronskianOver H).coeff (4*d-2) = _
    rw [← binaryDehomogenize_wronskian (by omega : 0 < d) H,
      binaryDehomogenize_eq_ofFn _ hhom,
      Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega),binary_top_value _ hhom]
    rfl
  rw [← htop,← hdeg,Polynomial.coeff_natDegree]
  apply Polynomial.leadingCoeff_ne_zero.mpr
  intro hzero
  rw [hzero,Polynomial.natDegree_zero] at hdeg
  omega

theorem exists_reverseWronskian_ne_zero {d : ℕ} (hd : 2 ≤ d) (t : ℂ) :
    ∃ H : Parameter d, (reverseWronskian H).eval t ≠ 0 := by
  by_cases ht : t = 0
  · subst t
    simpa only [reverseWronskian_eval] using exists_binaryWronskian_infinity_ne_zero hd
  · obtain ⟨H,hH⟩ := exists_affineWronskian_ne_zero (by omega : 0 < d) (1/t)
    refine ⟨H,?_⟩
    rw [reverseWronskian_eval,binaryEval_affine_ratio (4*d-2) _
      (binaryWronskianOver_homogeneous H) t 1 ht,
      binaryWronskian_affine_eval (by omega : 0 < d)]
    exact mul_ne_zero (pow_ne_zero _ ht) hH

theorem exists_reverseCriticalCoefficients_pivot {d : ℕ} (hd : 2 ≤ d) (t : ℂ) :
    ∃ j : SymIndex d, (reverseCriticalCoefficients d j).eval t ≠ 0 := by
  classical
  obtain ⟨H,hH⟩ := exists_reverseWronskian_ne_zero hd t
  by_contra! hbad
  apply hH
  rw [← linearCriticalValue_reverse]
  simp [linearCriticalValue,hbad]

theorem reverseChart_openCritical_of_root {d : ℕ} (hd : 0 < d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d) (hH : H ≠ 0)
    (hD : (reverseDenominator d).eval t ≠ 0)
    (hW : linearCriticalValue (reverseCriticalCoefficients d) t H = 0) :
    OpenCritical (reverseChartVector d c t) H := by
  refine ⟨hH,t,1,c,Or.inr one_ne_zero,hc,?_,?_,?_⟩
  · intro i
    simp [reverseChartVector,veronese]
  · rwa [← reverseDenominator_eval]
  · apply (parameterCritical_iff hd H (Or.inr one_ne_zero)).mpr
    rw [← reverseWronskian_eval,← linearCriticalValue_reverse]
    exact hW

theorem reverseChart_incidence_of_root {d : ℕ} (hd : 2 ≤ d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d) (hH : H ≠ 0)
    (hW : (reverseWronskian H).eval t = 0) :
    Incidence d (reverseChartVector d c t) H := by
  obtain ⟨j,hj⟩ := exists_reverseCriticalCoefficients_pivot hd t
  apply chart_incidence_of_root d (reverseChartVector d c)
    (by unfold reverseChartVector; fun_prop) (reverseCriticalCoefficients d)
    (reverseDenominator d) (reverseDenominator_ne_zero d)
    (fun s A hA hD hroot => reverseChart_openCritical_of_root (by omega) c s hc A hA hD hroot)
    t H hH (reverseChartVector_onCurve d c t hc) j hj
  rwa [linearCriticalValue_reverse]

theorem reverseChart_ramification_of_double_root {d : ℕ} (hd : 2 ≤ d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d) (hH : H ≠ 0)
    (hW : (reverseWronskian H).eval t = 0)
    (hW' : (reverseWronskian H).derivative.eval t = 0) :
    Ramification d (reverseChartVector d c t) H := by
  obtain ⟨j,hj⟩ := exists_reverseCriticalCoefficients_pivot hd t
  apply chart_ramification_of_double_root d (reverseChartVector d c)
    (by unfold reverseChartVector; fun_prop) (reverseCriticalCoefficients d)
    (reverseDenominator d) (reverseDenominator_ne_zero d)
    (fun s A hA hD hroot => reverseChart_openCritical_of_root (by omega) c s hc A hA hD hroot)
    t H hH (reverseChartVector_onCurve d c t hc) j hj
    (by rwa [linearCriticalValue_reverse])
    (by rwa [linearCriticalPolynomial_reverse])
    (reverseChartVelocity d c t) (hasDerivAt_reverseChartVector d c t)
    (reverseChart_tangents_independent d (by omega) c t hc)

#assert_trust kernel reverseWronskian_derivative_eval
#assert_trust kernel exists_binaryWronskian_infinity_ne_zero
#assert_trust kernel exists_reverseCriticalCoefficients_pivot
#assert_trust kernel reverseChart_openCritical_of_root
#assert_trust kernel reverseChart_incidence_of_root
#assert_trust kernel reverseChart_ramification_of_double_root
#print axioms reverseChart_ramification_of_double_root
end NLA.Proofs.TR26
