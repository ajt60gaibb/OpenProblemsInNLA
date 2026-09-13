/- Complete exact MI-03 formalization of Matthew J. Colbrook's argument.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.
AI-assisted; Apache 2.0. LeanCert audits the kernel trust of this exact proof;
no numerical interval certificate or phase approximation is used. -/
import NLA.MI03.Sharpness
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI03

theorem sharpness_witness_proved (k : ℕ) (hk : 2 ≤ k) :
    (∀ j : Fin k, ‖WithLp.toLp 2 (witnessVector k j)‖ = (1 : ℝ)) ∧
    (∀ j : Fin k, operatorNorm (witness k j) = 1) ∧
    (∀ j : Fin k, matrixModulus (witness k j) =
      outerProduct (witnessVector k j) (witnessVector k j)) ∧
    summandSum (witness k) = ((k : ℂ) / 2) • firstProjection ∧
    modulusSum (witness k) = witnessModulusSum k ∧
    matrixModulus (summandSum (witness k)) - modulusSum (witness k) =
      witnessDifference k := by
  exact ⟨witnessVector_norm k hk, witness_norm k hk, witness_modulus k hk,
    witness_sum k hk, witness_modulus_sum k hk, witness_difference k hk⟩

theorem lower_bound_proved (k : ℕ) (hk : 2 ≤ k) (c : ℝ)
    (hc : AdmissibleConstant k c) : (k : ℝ) / 4 ≤ c := by
  have hPSD := hc.2 2 (by decide) (witness k) (fun j => (witness_norm k hk j).le)
  have he : errorGap (witness k) c = (c : ℂ) • (1 : Mat 2) - witnessDifference k := by
    rw [← witness_difference k hk]
    simp only [errorGap]
    abel
  rw [he] at hPSD
  have hd := hPSD.diag_nonneg (i := (0 : Fin 2))
  have hreal := (Complex.nonneg_iff.mp hd).1
  norm_num [witnessDifference, Matrix.smul_apply, smul_eq_mul] at hreal
  linarith

theorem sharp_constant_proved (k : ℕ) (hk : 2 ≤ k) :
    IsLeast (admissibleConstants k) ((k : ℝ) / 4) ∧
    sharpConstant k = (k : ℝ) / 4 := by
  have hl : IsLeast (admissibleConstants k) ((k : ℝ) / 4) :=
    ⟨universal_upper_bound_proved k hk, fun c hc => lower_bound_proved k hk c hc⟩
  exact ⟨hl, hl.csInf_eq⟩

theorem odd_contraction_conjecture_proved : OddContractionConjecture := by
  intro k hk _hodd
  exact (sharp_constant_proved k (by omega)).2

#assert_trust kernel modulus_semantics_proved
#print axioms modulus_semantics_proved
#assert_trust kernel contraction_modulus_proved
#print axioms contraction_modulus_proved
#assert_trust kernel positive_decomposition_proved
#print axioms positive_decomposition_proved
#assert_trust kernel universal_upper_bound_proved
#print axioms universal_upper_bound_proved
#assert_trust kernel root_of_unity_data_proved
#print axioms root_of_unity_data_proved
#assert_trust kernel sharpness_witness_proved
#print axioms sharpness_witness_proved
#assert_trust kernel sharp_constant_proved
#print axioms sharp_constant_proved
#assert_trust kernel odd_contraction_conjecture_proved
#print axioms odd_contraction_conjecture_proved

end NLA.MI03
