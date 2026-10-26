import NLA.Proofs.TR26.FiniteJetPrimeImage
import NLA.Proofs.TR26.ProjectiveRamification

/-! The finite Taylor image and the two original projective charts. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem finiteDoubleWronskianImage_iff_affine_partials {d : ℕ} (hd : 2 ≤ d)
    (H : Parameter d) :
    H ∈ finiteDoubleWronskianImage d ↔ H ≠ 0 ∧ ∃ t : ℂ,
      binaryEval (binaryDenominator d) 1 t ≠ 0 ∧
      binaryEval (MvPolynomial.pderiv 0 (binaryWronskian H)) 1 t = 0 ∧
      binaryEval (MvPolynomial.pderiv 1 (binaryWronskian H)) 1 t = 0 := by
  constructor
  · rintro ⟨hH,t,hD,hW,hW'⟩
    refine ⟨hH,t,?_,?_⟩
    · rwa [binaryDenominator_eval,← affineDenominator_eval_eq_source]
    · exact (affineChart_ramification_iff_binary_partials hd 1 t one_ne_zero H hH).mp
        ((affineChart_ramification_iff hd 1 t one_ne_zero H hH).mpr ⟨hW,hW'⟩)
  · rintro ⟨hH,t,hD,ha,hb⟩
    refine ⟨hH,t,?_,?_⟩
    · rwa [binaryDenominator_eval,← affineDenominator_eval_eq_source] at hD
    · exact (affineChart_ramification_iff hd 1 t one_ne_zero H hH).mp
        ((affineChart_ramification_iff_binary_partials hd 1 t one_ne_zero H hH).mpr ⟨ha,hb⟩)

theorem mem_finiteDoubleWronskianImage_of_binary_partials {d : ℕ} (hd : 2 ≤ d)
    (H : Parameter d) (hH : H ≠ 0) (a b : ℂ) (ha : a ≠ 0)
    (hD : binaryEval (binaryDenominator d) a b ≠ 0)
    (h0 : binaryEval (MvPolynomial.pderiv 0 (binaryWronskian H)) a b = 0)
    (h1 : binaryEval (MvPolynomial.pderiv 1 (binaryWronskian H)) a b = 0) :
    H ∈ finiteDoubleWronskianImage d := by
  apply (finiteDoubleWronskianImage_iff_affine_partials hd H).mpr
  refine ⟨hH,b/a,?_,(binaryWronskian_partial_affine_zero_iff H 0 a b ha).mp h0,
    (binaryWronskian_partial_affine_zero_iff H 1 a b ha).mp h1⟩
  intro hz
  apply hD
  rw [binaryEval_affine_ratio (2*d) _ (binaryDenominatorOver_homogeneous ℂ d) a b ha,hz,mul_zero]

theorem finiteDoubleWronskianImage_subset_nonisotropicImage {d : ℕ} (hd : 2 ≤ d) :
    finiteDoubleWronskianImage d ⊆ NonisotropicImage d := by
  intro H hH
  obtain ⟨hH,t,hD,ha,hb⟩ := (finiteDoubleWronskianImage_iff_affine_partials hd H).mp hH
  exact (nonisotropicImage_iff_binary_partials hd H).mpr ⟨hH,1,t,Or.inl one_ne_zero,hD,ha,hb⟩

#assert_trust kernel finiteDoubleWronskianImage_iff_affine_partials
#assert_trust kernel mem_finiteDoubleWronskianImage_of_binary_partials
#assert_trust kernel finiteDoubleWronskianImage_subset_nonisotropicImage
#print axioms finiteDoubleWronskianImage_subset_nonisotropicImage
end NLA.Proofs.TR26
