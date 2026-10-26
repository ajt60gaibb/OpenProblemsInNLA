import NLA.Proofs.TR26.FixedDiscriminantSpecialization
import NLA.Proofs.TR26.IsotropicFactor

/-! The actual Wronskian-family discriminant in independent symmetric-matrix
coordinates. Homogeneity is proved from the real coefficient expressions; no
nonzero, reducedness, or factor-multiplicity conclusion is assumed here. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

/-- Every binary coefficient has one fixed parameter degree. -/
def CoefficientsHomogeneous {ι : Type*} (P : BinaryForm (MvPolynomial ι ℂ)) (n : ℕ) : Prop :=
  ∀ e : Fin 2 →₀ ℕ, (MvPolynomial.coeff e P).IsHomogeneous n

namespace CoefficientsHomogeneous
variable {ι : Type*} {P Q : BinaryForm (MvPolynomial ι ℂ)} {n m : ℕ}

theorem C {c : MvPolynomial ι ℂ} (hc : c.IsHomogeneous n) :
    CoefficientsHomogeneous (MvPolynomial.C c : BinaryForm (MvPolynomial ι ℂ)) n := by
  classical
  intro e
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact hc
  · exact isHomogeneous_zero _ _ _

theorem X (i : Fin 2) : CoefficientsHomogeneous (MvPolynomial.X i : BinaryForm (MvPolynomial ι ℂ)) 0 := by
  classical
  intro e
  simp only [MvPolynomial.X, MvPolynomial.coeff_monomial]
  split_ifs
  · exact isHomogeneous_one _ _
  · exact isHomogeneous_zero _ _ _

theorem mul (hP : CoefficientsHomogeneous P n) (hQ : CoefficientsHomogeneous Q m) :
    CoefficientsHomogeneous (P * Q) (n + m) := by
  classical
  intro e
  rw [MvPolynomial.coeff_mul]
  apply IsHomogeneous.sum
  intro z _
  exact (hP z.1).mul (hQ z.2)

theorem sub (hP : CoefficientsHomogeneous P n) (hQ : CoefficientsHomogeneous Q n) :
    CoefficientsHomogeneous (P - Q) n := by
  intro e
  rw [MvPolynomial.coeff_sub]
  exact (hP e).sub (hQ e)

theorem sum {κ : Type*} (s : Finset κ) (F : κ → BinaryForm (MvPolynomial ι ℂ))
    (hF : ∀ i ∈ s, CoefficientsHomogeneous (F i) n) :
    CoefficientsHomogeneous (∑ i ∈ s, F i) n := by
  intro e
  rw [MvPolynomial.coeff_sum]
  exact IsHomogeneous.sum s _ _ (fun i hi => hF i hi e)

theorem pow_zero_degree (hP : CoefficientsHomogeneous P 0) (k : ℕ) :
    CoefficientsHomogeneous (P ^ k) 0 := by
  induction k with
  | zero => simpa only [pow_zero, MvPolynomial.C_1] using
      (C (isHomogeneous_one ι ℂ))
  | succ k ih =>
    simpa only [pow_succ, zero_add] using mul ih hP

theorem pderiv (hP : CoefficientsHomogeneous P n) (i : Fin 2) :
    CoefficientsHomogeneous (MvPolynomial.pderiv i P) n := by
  intro e
  rw [MvPolynomial.coeff_pderiv]
  have h := (hP (e + Finsupp.single i 1)).C_mul (((e i + 1 : ℕ) : ℂ))
  simpa [mul_comm] using h
end CoefficientsHomogeneous

theorem binaryVeronese_coefficientsHomogeneous (d : ℕ) (i : Index d) :
    CoefficientsHomogeneous (binaryVeroneseOver (ParameterRing d) d i) 0 := by
  unfold binaryVeroneseOver
  simpa only [zero_add] using
    ((CoefficientsHomogeneous.X (ι := SymIndex d) 0).pow_zero_degree (d - i.val)).mul
      ((CoefficientsHomogeneous.X (ι := SymIndex d) 1).pow_zero_degree i.val)

theorem binaryDenominator_coefficientsHomogeneous (d : ℕ) :
    CoefficientsHomogeneous (binaryDenominatorOver (ParameterRing d) d) 0 := by
  apply CoefficientsHomogeneous.sum
  intro i _
  simpa only [zero_add] using (binaryVeronese_coefficientsHomogeneous d i).mul
    (binaryVeronese_coefficientsHomogeneous d i)

theorem binaryNumerator_coefficientsHomogeneous (d : ℕ) :
    CoefficientsHomogeneous
      (binaryNumeratorOver (fun ij : SymIndex d => MvPolynomial.X ij : SymIndex d → ParameterRing d)) 1 := by
  apply CoefficientsHomogeneous.sum
  intro i _
  apply CoefficientsHomogeneous.sum
  intro j _
  have hentry : (coordinateEntry (fun ij : SymIndex d => MvPolynomial.X ij : SymIndex d → ParameterRing d)
      i j).IsHomogeneous 1 := by
    unfold coordinateEntry
    split_ifs <;> exact isHomogeneous_X ℂ _
  simpa only [add_zero] using ((CoefficientsHomogeneous.C hentry).mul
    (binaryVeronese_coefficientsHomogeneous d i)).mul (binaryVeronese_coefficientsHomogeneous d j)

theorem binaryWronskian_coefficientsHomogeneous (d : ℕ) :
    CoefficientsHomogeneous
      (binaryWronskianOver (fun ij : SymIndex d => MvPolynomial.X ij : SymIndex d → ParameterRing d)) 1 := by
  unfold binaryWronskianOver
  have hN := binaryNumerator_coefficientsHomogeneous d
  have hD := binaryDenominator_coefficientsHomogeneous d
  have hleft := (hN.pderiv 1).mul (hD.pderiv 0)
  have hright := (hN.pderiv 0).mul (hD.pderiv 1)
  have hdiff : CoefficientsHomogeneous
      (MvPolynomial.pderiv 1 (binaryNumeratorOver (fun ij : SymIndex d => MvPolynomial.X ij : SymIndex d → ParameterRing d)) *
        MvPolynomial.pderiv 0 (binaryDenominatorOver (ParameterRing d) d) -
       MvPolynomial.pderiv 0 (binaryNumeratorOver (fun ij : SymIndex d => MvPolynomial.X ij : SymIndex d → ParameterRing d)) *
        MvPolynomial.pderiv 1 (binaryDenominatorOver (ParameterRing d) d)) 1 := by
    simpa only [add_zero] using hleft.sub hright
  have hc : (algebraMap ℂ (ParameterRing d) ((2 * d : ℂ)⁻¹)).IsHomogeneous 0 :=
    isHomogeneous_C _ _
  simpa only [zero_add] using (CoefficientsHomogeneous.C hc).mul hdiff

theorem wronskian_family_coefficient_homogeneous (d : ℕ) (i : Fin (4 * d - 2 + 1)) :
    (wronskianCoefficientsOver
      (fun ij : SymIndex d => MvPolynomial.X ij : SymIndex d → ParameterRing d) i).IsHomogeneous 1 :=
  binaryWronskian_coefficientsHomogeneous d _

/-- The fixed-degree discriminant evaluated on the actual unweighted Wronskian family. -/
def wronskianFamilyDiscriminant (d : ℕ) : ParameterRing d :=
  MvPolynomial.aeval (wronskianCoefficientsOver
    (fun ij : SymIndex d => MvPolynomial.X ij : SymIndex d → ParameterRing d))
      (BinaryDiscriminant.fixedDiscriminant (4 * d - 2))

theorem wronskianFamilyDiscriminant_homogeneous {d : ℕ} (hd : 1 ≤ d) :
    (wronskianFamilyDiscriminant d).IsHomogeneous (8 * d - 6) := by
  have h := BinaryDiscriminant.fixedDiscriminant_aeval_homogeneous (4 * d - 2)
    (wronskianCoefficientsOver (fun ij : SymIndex d => MvPolynomial.X ij : SymIndex d → ParameterRing d))
    (wronskian_family_coefficient_homogeneous d)
  have hdegree : 2 * (4 * d - 2) - 2 = 8 * d - 6 := by omega
  simpa only [wronskianFamilyDiscriminant, hdegree] using h

#assert_trust kernel binaryWronskian_coefficientsHomogeneous
#assert_trust kernel wronskian_family_coefficient_homogeneous
#assert_trust kernel wronskianFamilyDiscriminant_homogeneous
#print axioms wronskianFamilyDiscriminant_homogeneous
end NLA.Proofs.TR26
