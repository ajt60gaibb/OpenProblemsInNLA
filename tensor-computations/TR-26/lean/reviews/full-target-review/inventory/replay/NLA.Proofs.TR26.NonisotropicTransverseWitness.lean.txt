import NLA.Proofs.TR26.NonisotropicDoubleWitness
import NLA.Proofs.TR26.IsotropicTransverseWitness

/-! A nonzero first variation of the actual family discriminant at a genuine
nonisotropic ordinary-double Wronskian. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26 Polynomial

theorem exists_nonisotropic_family_transverse {d : ℕ} (hd : 2 ≤ d) :
    ∃ H K : Parameter d, ∃ δ : ℂ,
      H ∈ finiteDoubleWronskianImage d ∧
      MvPolynomial.eval H (isotropicEvaluationFactor d) ≠ 0 ∧
      HasDerivAt (fun (ε : ℂ) => MvPolynomial.eval (H + ε • K)
        (wronskianFamilyDiscriminant d)) δ 0 ∧ δ ≠ 0 := by
  obtain ⟨H, S, hfinite, hE, hsep, hS0, hSdeg, hW⟩ :=
    exists_nonisotropic_ordinary_double_Wronskian hd
  obtain ⟨K, hK0, hKdeg⟩ := exists_nonisotropic_transverse_direction hd
  let V := affineWronskian K
  let δ : ℂ := BinaryDiscriminant.doubleRootSplitScale S * S.eval 0 ^ 3 * V.eval 0
  have hsize : 2 + S.natDegree = 4 * d - 2 := by omega
  have hSpos : 0 < S.natDegree := by omega
  have hVdeg : V.natDegree ≤ 2 + S.natDegree := by rw [hsize]; exact hKdeg
  have hVar := BinaryDiscriminant.hasDerivAt_fixedDiscriminant_ordinary_double_root
    0 S V hSpos hVdeg hS0
  rw [hsize] at hVar
  simp only [Polynomial.C_0, sub_zero] at hVar
  refine ⟨H, K, δ, hfinite, hE, ?_, ?_⟩
  · convert! hVar using 1
    ext ε
    rw [eval_wronskianFamilyDiscriminant_affine (by omega), affineWronskian_parameter_line, hW]
  · exact BinaryDiscriminant.fixedDiscriminant_ordinary_double_root_derivative_ne_zero
      0 S V hSpos hsep hS0 hK0

#assert_trust kernel exists_nonisotropic_family_transverse
#print axioms exists_nonisotropic_family_transverse
end NLA.Proofs.TR26
