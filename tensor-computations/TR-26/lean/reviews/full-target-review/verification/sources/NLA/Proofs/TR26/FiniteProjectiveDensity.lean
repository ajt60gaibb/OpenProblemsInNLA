import NLA.Proofs.TR26.FiniteProjectiveCharts
import NLA.Proofs.TR26.MatrixReversal

/-! The finite Taylor image is dense in the full nonisotropic projection.
Deleting the root-coordinate hyperplane from the reversed polynomial Taylor
map gives a subset of the finite chart; polynomial-image ideals restore the
omitted root zero. Thus the point at infinity adds no extra component. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

def reverseMatrixJetSubstitution (d : ℕ) : ParameterRing d →ₐ[ℂ] MatrixJetRing d :=
  MvPolynomial.aeval (fun ij => matrixJetPolynomial d (reverseSymIndex d ij))

theorem reverseMatrixJetSubstitution_coordinates (d : ℕ) (x : MatrixJetVariable d → ℂ) :
    polynomialImageCoordinates (reverseMatrixJetSubstitution d) x =
      reverseParameter (matrixJetMap d x) := by
  ext ij
  simp [polynomialImageCoordinates,reverseMatrixJetSubstitution,reverseParameterOver,matrixJetMap]

theorem exists_reverseMatrixJetSubstitution_X_ne_zero {d : ℕ} (hd : 2 ≤ d) :
    ∃ ij : SymIndex d, reverseMatrixJetSubstitution d (MvPolynomial.X ij) ≠ 0 := by
  obtain ⟨ij,hij⟩ := exists_matrixJetPolynomial_ne_zero hd
  refine ⟨reverseSymIndex d ij,?_⟩
  simp only [reverseMatrixJetSubstitution,MvPolynomial.aeval_X]
  rwa [reverseSymIndex_involutive d ij]

theorem reverseMatrixJetMap_mem_finite_of_root_ne_zero {d : ℕ} (hd : 2 ≤ d)
    (x : MatrixJetVariable d → ℂ)
    (hD : MvPolynomial.eval x (matrixJetDenominator d) ≠ 0)
    (hr : x (Sum.inl (Sum.inl 0)) ≠ 0)
    (hH : reverseParameter (matrixJetMap d x) ≠ 0) :
    reverseParameter (matrixJetMap d x) ∈ finiteDoubleWronskianImage d := by
  let r := x (Sum.inl (Sum.inl 0))
  have hDn : (affineDenominator d).eval r ≠ 0 := by
    rw [eval_matrixJetDenominator] at hD
    exact (mul_ne_zero_iff.mp hD).2
  have hparts : binaryEval (MvPolynomial.pderiv 0 (binaryWronskian (matrixJetMap d x))) 1 r = 0 ∧
      binaryEval (MvPolynomial.pderiv 1 (binaryWronskian (matrixJetMap d x))) 1 r = 0 :=
    (affineChart_ramification_iff_binary_partials hd 1 r one_ne_zero _
      ((reverseParameter_ne_zero_iff _).mp hH)).mp
      ((affineChart_ramification_iff hd 1 r one_ne_zero _
        ((reverseParameter_ne_zero_iff _).mp hH)).mpr (matrixJetMap_double_root hd x hDn))
  have hp := (binaryWronskian_reverse_double_root_iff (matrixJetMap d x) r 1).mpr hparts
  apply mem_finiteDoubleWronskianImage_of_binary_partials hd _ hH r 1 hr _ hp.1 hp.2
  rw [binaryDenominator_eval_swap,binaryDenominator_eval,← affineDenominator_eval_eq_source]
  exact hDn

theorem reverseMatrixJet_open_deleted_subset_finite {d : ℕ} (hd : 2 ≤ d) :
    principalOpenPolynomialImage (reverseMatrixJetSubstitution d)
      (matrixJetDenominator d * MvPolynomial.X (Sum.inl (Sum.inl 0))) ⊆
      finiteDoubleWronskianImage d := by
  rintro H ⟨x,hD,hH,rfl⟩
  rw [map_mul,MvPolynomial.eval_X] at hD
  rw [reverseMatrixJetSubstitution_coordinates] at hH ⊢
  exact reverseMatrixJetMap_mem_finite_of_root_ne_zero hd x
    (mul_ne_zero_iff.mp hD).1 (mul_ne_zero_iff.mp hD).2 hH

theorem vanishing_on_reverse_finite_of_vanishing_on_finite {d : ℕ} (hd : 2 ≤ d)
    (f : ParameterRing d)
    (hf : f ∈ MvPolynomial.vanishingIdeal ℂ (finiteDoubleWronskianImage d))
    (J : Parameter d) (hJ : J ∈ finiteDoubleWronskianImage d) :
    MvPolynomial.eval (reverseParameter J) f = 0 := by
  have hfdel : f ∈ MvPolynomial.vanishingIdeal ℂ
      (principalOpenPolynomialImage (reverseMatrixJetSubstitution d)
        (matrixJetDenominator d * MvPolynomial.X (Sum.inl (Sum.inl 0)))) :=
    fun H hH => hf H (reverseMatrixJet_open_deleted_subset_finite hd hH)
  obtain ⟨ij,hij⟩ := exists_reverseMatrixJetSubstitution_X_ne_zero hd
  rw [vanishingIdeal_principalOpenPolynomialImage_mul _ _ _
    (matrixJetDenominator_ne_zero d) (MvPolynomial.X_ne_zero _) ij hij] at hfdel
  rw [finiteDoubleWronskianImage_eq_matrixJetImage hd] at hJ
  obtain ⟨x,hD,hx,hJx⟩ := hJ
  apply hfdel (reverseParameter J)
  refine ⟨x,hD,?_,?_⟩
  · rw [reverseMatrixJetSubstitution_coordinates]
    exact (reverseParameter_ne_zero_iff _).mpr hx
  · rw [reverseMatrixJetSubstitution_coordinates,hJx]

theorem nonisotropicImage_vanishingIdeal_eq_finite {d : ℕ} (hd : 2 ≤ d) :
    MvPolynomial.vanishingIdeal ℂ (NonisotropicImage d) =
      MvPolynomial.vanishingIdeal ℂ (finiteDoubleWronskianImage d) := by
  apply le_antisymm
  · intro f hf H hH
    exact hf H (finiteDoubleWronskianImage_subset_nonisotropicImage hd hH)
  · intro f hf H hH
    obtain ⟨hH,a,b,hab,hD,h0,h1⟩ := (nonisotropicImage_iff_binary_partials hd H).mp hH
    by_cases ha : a ≠ 0
    · exact hf H (mem_finiteDoubleWronskianImage_of_binary_partials hd H hH a b ha hD h0 h1)
    · have hb : b ≠ 0 := hab.resolve_left ha
      have hrH : reverseParameter H ≠ 0 := (reverseParameter_ne_zero_iff H).mpr hH
      have hp := (binaryWronskian_reverse_double_root_iff H b a).mpr ⟨h0,h1⟩
      have hJ : reverseParameter H ∈ finiteDoubleWronskianImage d :=
        mem_finiteDoubleWronskianImage_of_binary_partials hd _ hrH b a hb
          (by rwa [binaryDenominator_eval_swap]) hp.1 hp.2
      have hh := vanishing_on_reverse_finite_of_vanishing_on_finite hd f hf _ hJ
      change MvPolynomial.eval (reverseParameterOver (reverseParameterOver H)) f = 0 at hh
      rw [reverseParameterOver_involutive d H] at hh
      exact hh

#assert_trust kernel reverseMatrixJetSubstitution_coordinates
#assert_trust kernel exists_reverseMatrixJetSubstitution_X_ne_zero
#assert_trust kernel reverseMatrixJetMap_mem_finite_of_root_ne_zero
#assert_trust kernel reverseMatrixJet_open_deleted_subset_finite
#assert_trust kernel vanishing_on_reverse_finite_of_vanishing_on_finite
#assert_trust kernel nonisotropicImage_vanishingIdeal_eq_finite
#print axioms nonisotropicImage_vanishingIdeal_eq_finite
end NLA.Proofs.TR26
