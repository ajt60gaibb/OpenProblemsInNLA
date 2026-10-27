import NLA.Proofs.TR26.MatrixJetImage
import NLA.Proofs.TR26.PolynomialImageIdeal

/-! The exact finite nonisotropic double-Wronskian image has a prime vanishing
ideal. This is the kernel of the concrete full-matrix Taylor substitution. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

def matrixJetSubstitution (d : ℕ) : ParameterRing d →ₐ[ℂ] MatrixJetRing d :=
  MvPolynomial.aeval (matrixJetPolynomial d)

theorem matrixJetSubstitution_coordinates (d : ℕ) (x : MatrixJetVariable d → ℂ) :
    polynomialImageCoordinates (matrixJetSubstitution d) x = matrixJetMap d x := by
  ext ij
  simp [polynomialImageCoordinates, matrixJetSubstitution, matrixJetMap]

theorem finiteDoubleWronskianImage_eq_principalOpenImage {d : ℕ} (hd : 2 ≤ d) :
    finiteDoubleWronskianImage d =
      principalOpenPolynomialImage (matrixJetSubstitution d) (matrixJetDenominator d) := by
  rw [finiteDoubleWronskianImage_eq_matrixJetImage hd]
  ext H
  simp only [principalOpenPolynomialImage, Set.mem_setOf_eq, matrixJetSubstitution_coordinates]
  constructor
  · rintro ⟨x, hD, hx, hH⟩
    exact ⟨x, hD, hx, hH.symm⟩
  · rintro ⟨x, hD, hx, hH⟩
    exact ⟨x, hD, hx, hH.symm⟩

theorem finiteDoubleWronskianImage_vanishingIdeal_eq_ker {d : ℕ} (hd : 2 ≤ d) :
    MvPolynomial.vanishingIdeal ℂ (finiteDoubleWronskianImage d) =
      RingHom.ker (matrixJetSubstitution d).toRingHom := by
  rw [finiteDoubleWronskianImage_eq_principalOpenImage hd]
  obtain ⟨ij, hij⟩ := exists_matrixJetPolynomial_ne_zero hd
  exact vanishingIdeal_principalOpenPolynomialImage_eq_ker _ _
    (matrixJetDenominator_ne_zero d) ij (by simpa [matrixJetSubstitution] using hij)

theorem finiteDoubleWronskianImage_vanishingIdeal_isPrime {d : ℕ} (hd : 2 ≤ d) :
    (MvPolynomial.vanishingIdeal ℂ (finiteDoubleWronskianImage d)).IsPrime := by
  rw [finiteDoubleWronskianImage_vanishingIdeal_eq_ker hd]
  exact RingHom.ker_isPrime _

theorem finiteDoubleWronskianImage_mem_vanishingIdeal_iff {d : ℕ} (hd : 2 ≤ d)
    (f : ParameterRing d) :
    f ∈ MvPolynomial.vanishingIdeal ℂ (finiteDoubleWronskianImage d) ↔
      matrixJetSubstitution d f = 0 := by
  rw [finiteDoubleWronskianImage_vanishingIdeal_eq_ker hd]
  rfl

#assert_trust kernel matrixJetSubstitution_coordinates
#assert_trust kernel finiteDoubleWronskianImage_eq_principalOpenImage
#assert_trust kernel finiteDoubleWronskianImage_vanishingIdeal_eq_ker
#assert_trust kernel finiteDoubleWronskianImage_vanishingIdeal_isPrime
#assert_trust kernel finiteDoubleWronskianImage_mem_vanishingIdeal_iff
#print axioms finiteDoubleWronskianImage_vanishingIdeal_isPrime
end NLA.Proofs.TR26
