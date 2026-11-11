import NLA.Proofs.TR26.FamilyDiscriminant
import NLA.Proofs.TR26.Wronskian

/-! Exact evaluation of the parameter-family discriminant against the actual
Wronskian and both genuine homogeneous partial derivatives. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem eval_coordinateEntry (d : ℕ) (H : Parameter d) (i j : Index d) :
    MvPolynomial.eval H (coordinateEntry
      (fun ij : SymIndex d => MvPolynomial.X ij : SymIndex d → ParameterRing d) i j) =
      coordinateEntry H i j := by
  unfold coordinateEntry
  split_ifs <;> exact eval_X _

theorem map_binaryVeroneseOver {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (d : ℕ) (i : Index d) :
    MvPolynomial.map φ (binaryVeroneseOver R d i) = binaryVeroneseOver S d i := by
  simp [binaryVeroneseOver]

theorem map_binaryDenominatorOver {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (d : ℕ) :
    MvPolynomial.map φ (binaryDenominatorOver R d) = binaryDenominatorOver S d := by
  simp only [binaryDenominatorOver, map_sum, map_mul, map_binaryVeroneseOver]

theorem map_parameter_binaryNumerator (d : ℕ) (H : Parameter d) :
    MvPolynomial.map (MvPolynomial.eval H) (binaryNumeratorOver
      (fun ij : SymIndex d => MvPolynomial.X ij : SymIndex d → ParameterRing d)) =
      binaryNumerator H := by
  simp only [binaryNumeratorOver, map_sum, map_mul, map_C, eval_coordinateEntry,
    map_binaryVeroneseOver]

theorem map_parameter_binaryWronskian (d : ℕ) (H : Parameter d) :
    MvPolynomial.map (MvPolynomial.eval H) (binaryWronskianOver
      (fun ij : SymIndex d => MvPolynomial.X ij : SymIndex d → ParameterRing d)) =
      binaryWronskian H := by
  have hN := map_parameter_binaryNumerator d H
  have hD := map_binaryDenominatorOver (MvPolynomial.eval H) d
  have hderN (i : Fin 2) :
      MvPolynomial.map (MvPolynomial.eval H) (MvPolynomial.pderiv i (binaryNumeratorOver
        (fun ij : SymIndex d => MvPolynomial.X ij : SymIndex d → ParameterRing d))) =
        MvPolynomial.pderiv i (binaryNumerator H) := by
    rw [← MvPolynomial.pderiv_map, hN]
  have hderD (i : Fin 2) :
      MvPolynomial.map (MvPolynomial.eval H) (MvPolynomial.pderiv i
        (binaryDenominatorOver (ParameterRing d) d)) =
        MvPolynomial.pderiv i (binaryDenominator d) := by
    rw [← MvPolynomial.pderiv_map, hD]
  unfold binaryWronskianOver
  simp only [map_mul, map_sub, map_C, hderN, hderD]
  congr 2
  simp

theorem eval_wronskian_family_coefficient (d : ℕ) (H : Parameter d)
    (i : Fin (4 * d - 2 + 1)) :
    MvPolynomial.eval H (wronskianCoefficientsOver
      (fun ij : SymIndex d => MvPolynomial.X ij : SymIndex d → ParameterRing d) i) =
      wronskianCoefficientsOver H i := by
  unfold wronskianCoefficientsOver binaryCoeff
  rw [← MvPolynomial.coeff_map, map_parameter_binaryWronskian]

theorem eval_wronskianFamilyDiscriminant (d : ℕ) (H : Parameter d) :
    MvPolynomial.eval H (wronskianFamilyDiscriminant d) =
      MvPolynomial.eval (wronskianCoefficientsOver H)
        (BinaryDiscriminant.fixedDiscriminant (4 * d - 2)) := by
  unfold wronskianFamilyDiscriminant
  rw [BinaryDiscriminant.eval_specialized_fixedDiscriminant]
  simp only [eval_wronskian_family_coefficient]

theorem eval_wronskianFamilyDiscriminant_eq_zero_iff {d : ℕ} (hd : 1 ≤ d)
    (H : Parameter d) :
    MvPolynomial.eval H (wronskianFamilyDiscriminant d) = 0 ↔
      ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧
        binaryEval (MvPolynomial.pderiv 0 (binaryWronskian H)) a b = 0 ∧
        binaryEval (MvPolynomial.pderiv 1 (binaryWronskian H)) a b = 0 := by
  rw [eval_wronskianFamilyDiscriminant,
    BinaryDiscriminant.eval_fixedDiscriminant_eq_zero_iff_actual_partials (by omega : 2 ≤ 4 * d - 2)]
  have hrec : BinaryDiscriminant.binaryFromCoefficients (4 * d - 2)
      (wronskianCoefficientsOver H) = binaryWronskian H :=
    (binaryWronskianOver_reconstruct H).symm
  rw [hrec]

#assert_trust kernel map_parameter_binaryWronskian
#assert_trust kernel eval_wronskian_family_coefficient
#assert_trust kernel eval_wronskianFamilyDiscriminant
#assert_trust kernel eval_wronskianFamilyDiscriminant_eq_zero_iff
#print axioms eval_wronskianFamilyDiscriminant_eq_zero_iff
end NLA.Proofs.TR26
