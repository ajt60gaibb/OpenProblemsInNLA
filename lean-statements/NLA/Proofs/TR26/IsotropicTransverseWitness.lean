import NLA.Proofs.TR26.IsotropicWronskianWitness
import NLA.Proofs.TR26.OrdinaryDoubleRootVariation
import NLA.Proofs.TR26.FamilyDiscriminantNonzero
import NLA.Proofs.TR26.WronskianLinear

/-! Actual symmetric-matrix transverse witnesses above every isotropic
hyperplane. The perturbation lifts the constant numerator 1. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26 Polynomial

theorem wronskianCoefficients_eq_toFn {d : ℕ} (hd : 0 < d) (H : Parameter d) :
    wronskianCoefficientsOver H=Polynomial.toFn (4*d-2+1) (affineWronskian H) := by
  have hh : Polynomial.ofFn (4*d-2+1) (wronskianCoefficientsOver H)=affineWronskian H := by
    change Polynomial.ofFn (4*d-2+1) (binaryCoeff (4*d-2) (binaryWronskianOver H))=_
    rw [← binaryDehomogenize_eq_ofFn _ (binaryWronskianOver_homogeneous H),
      binaryDehomogenize_wronskian hd]
  have hh' := congrArg (Polynomial.toFn (4*d-2+1)) hh
  rw [Polynomial.toFn_comp_ofFn_eq_id] at hh'
  exact hh'

theorem eval_wronskianFamilyDiscriminant_affine {d : ℕ} (hd : 0 < d) (H : Parameter d) :
    MvPolynomial.eval H (wronskianFamilyDiscriminant d)=
      MvPolynomial.eval (Polynomial.toFn (4*d-2+1) (affineWronskian H))
        (BinaryDiscriminant.fixedDiscriminant (4*d-2)) := by
  rw [eval_wronskianFamilyDiscriminant,wronskianCoefficients_eq_toFn hd]

theorem affineNumerator_parameter_line {d : ℕ} (H K : Parameter d) (ε : ℂ) :
    affineNumerator (H+ε • K)=affineNumerator H+C ε*affineNumerator K := by
  change affineNumeratorLinear d (H+ε • K)=_
  rw [map_add,map_smul]
  rw [Polynomial.smul_eq_C_mul]
  rfl

theorem affineWronskian_parameter_line {d : ℕ} (H K : Parameter d) (ε : ℂ) :
    affineWronskian (H+ε • K)=affineWronskian H+C ε*affineWronskian K := by
  calc
    _ = affineWronskianLinear d (H+ε • K) := (affineWronskianLinear_apply _).symm
    _ = affineWronskianLinear d H+ε • affineWronskianLinear d K := by rw [map_add,map_smul]
    _ = _ := by rw [affineWronskianLinear_apply,affineWronskianLinear_apply,Polynomial.smul_eq_C_mul]

theorem exists_isotropic_family_transverse {d : ℕ} (hd : 2 ≤ d)
    {r : ℂ} (hr : r ∈ denominatorRoots d) :
    ∃ H K : Parameter d, ∃ δ : ℂ,
      MvPolynomial.eval H (numeratorEvaluationPolynomial d r)=0 ∧
      MvPolynomial.eval K (numeratorEvaluationPolynomial d r)=1 ∧
      HasDerivAt (fun (ε : ℂ) => MvPolynomial.eval (H+ε • K) (wronskianFamilyDiscriminant d)) δ 0 ∧
      δ ≠ 0 := by
  obtain ⟨H,S,hNr,hW,hSsep,hSdeg,hSr⟩ := exists_isotropic_ordinary_Wronskian hd hr
  obtain ⟨K,hK⟩ := affineNumerator_surjective_degreeLE d 1 (by simp)
  have hKwr : affineWronskian K=-(affineDenominator d).derivative := by
    change polynomialWronskian (affineNumerator K) (affineDenominator d)=_
    rw [hK,polynomialWronskian_one]
  let V : Polynomial ℂ := -(affineDenominator d).derivative
  let δ : ℂ := BinaryDiscriminant.doubleRootSplitScale S*S.eval r^3*V.eval r
  have hsize : 2+S.natDegree=4*d-2 := by omega
  have hSpos : 0 < S.natDegree := by omega
  have hVdeg : V.natDegree ≤ 2+S.natDegree := by
    dsimp [V]
    rw [natDegree_neg,natDegree_derivative,affineDenominator_natDegree]
    omega
  have hVr : V.eval r ≠ 0 := by
    simpa only [V,Polynomial.eval_neg] using neg_ne_zero.mpr (denominator_derivative_at_root_ne_zero hr)
  have hVar := BinaryDiscriminant.hasDerivAt_fixedDiscriminant_ordinary_double_root r S V hSpos hVdeg hSr
  rw [hsize] at hVar
  refine ⟨H,K,δ,?_,?_,?_,?_⟩
  · rwa [eval_numeratorEvaluationPolynomial]
  · rw [eval_numeratorEvaluationPolynomial,hK,Polynomial.eval_one]
  · convert! hVar using 1
    ext ε
    rw [eval_wronskianFamilyDiscriminant_affine (by omega),affineWronskian_parameter_line,hW,hKwr]
  · exact BinaryDiscriminant.fixedDiscriminant_ordinary_double_root_derivative_ne_zero r S V hSpos hSsep hSr hVr

#assert_trust kernel wronskianCoefficients_eq_toFn
#assert_trust kernel eval_wronskianFamilyDiscriminant_affine
#assert_trust kernel exists_isotropic_family_transverse
#print axioms exists_isotropic_family_transverse
end NLA.Proofs.TR26
