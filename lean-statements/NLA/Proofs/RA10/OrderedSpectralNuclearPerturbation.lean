import NLA.Proofs.RA10.HermitianPositivePartOrder
import NLA.Proofs.RA10.OrderedPSDLoewnerEigenvalue
import NLA.Proofs.RA10.SelectedCompressionOrderedSpectral

/-! RA-10, source Section 4: the coefficient-one nuclear perturbation bound
for all supplied ordered PSD spectra. No commutation, eigenvalue gap, or
positive-definiteness assumption is used. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

theorem spectralMatrix_factor {n : ℕ}
    (d : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.SpectralMatrix d Q = Q * Matrix.diagonal d * Q.transpose := by
  ext i j
  simp only [NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

theorem spectralMatrix_trace {n : ℕ}
    (d : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ a b, ∑ i, Q i a * Q i b = if a = b then 1 else 0) :
    Matrix.trace (NLA.Statements.RA10.SpectralMatrix d Q) = ∑ a, d a := by
  have hQtQ : Q.transpose * Q = 1 := by
    ext a b
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hQ a b
  rw [spectralMatrix_factor, Matrix.trace_mul_cycle, hQtQ, one_mul, Matrix.trace_diagonal]

/-- The source eigenvalue perturbation inequality, with coefficient exactly one. -/
theorem orderedPSDSpectral_nuclear_perturbation {n : ℕ}
    {X Y : Matrix (Fin n) (Fin n) ℝ} {x y : Fin n → ℝ}
    {QX QY : Matrix (Fin n) (Fin n) ℝ}
    (hX : NLA.Statements.RA10.OrderedPSDSpectralDecomposition X x QX)
    (hY : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Y y QY) :
    (∑ i : Fin n, |x i - y i|) ≤ NLA.Statements.RA10.NuclearNorm (X - Y) := by
  have hXpsd := (sourcePositiveSemidefinite_iff_mathlibPosSemidef X).mp
    (orderedPSDSpectralDecomposition_positiveSemidefinite hX)
  have hYpsd := (sourcePositiveSemidefinite_iff_mathlibPosSemidef Y).mp
    (orderedPSDSpectralDecomposition_positiveSemidefinite hY)
  have hJ : (X - Y).IsHermitian := hXpsd.1.sub hYpsd.1
  let T := hermitianPositivePart (X - Y)
  let U := Y + T
  have hT : Matrix.PosSemidef T := hermitianPositivePart_posSemidef (X - Y) hJ
  have hUX : Matrix.PosSemidef (U - X) := by
    have heq : U - X = T - (X - Y) := by dsimp [U]; abel
    rw [heq]
    exact hermitianPositivePart_sub_posSemidef (X - Y) hJ
  have hUY : Matrix.PosSemidef (U - Y) := by
    simpa [U] using hT
  obtain ⟨u, QU, hU⟩ := mathlibPosSemidef_exists_orderedPSD (hYpsd.add hT)
  have hxu (i : Fin n) : x i ≤ u i :=
    orderedPSDSpectral_eigenvalues_le_of_psd_sub hU hX
      ((sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mpr hUX) i
  have hyu (i : Fin n) : y i ≤ u i :=
    orderedPSDSpectral_eigenvalues_le_of_psd_sub hU hY
      ((sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mpr hUY) i
  have htraceX : Matrix.trace X = ∑ i, x i := by
    rw [hX.2.2.2, spectralMatrix_trace x QX hX.2.2.1]
  have htraceY : Matrix.trace Y = ∑ i, y i := by
    rw [hY.2.2.2, spectralMatrix_trace y QY hY.2.2.1]
  have htraceU : Matrix.trace U = ∑ i, u i := by
    change Matrix.trace (Y + T) = _
    rw [hU.2.2.2, spectralMatrix_trace u QU hU.2.2.1]
  calc
    (∑ i : Fin n, |x i - y i|) ≤ ∑ i : Fin n, (2 * u i - x i - y i) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact abs_le.mpr ⟨by linarith [hyu i], by linarith [hxu i]⟩
    _ = 2 * Matrix.trace U - Matrix.trace X - Matrix.trace Y := by
      rw [htraceU, htraceX, htraceY]
      simp only [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = 2 * Matrix.trace T - Matrix.trace (X - Y) := by
      simp only [U, Matrix.trace_add, Matrix.trace_sub]
      ring
    _ = NLA.Statements.RA10.NuclearNorm (X - Y) :=
      (nuclearNorm_eq_two_trace_positivePart_sub_trace (X - Y) hJ).symm

#assert_trust kernel orderedPSDSpectral_nuclear_perturbation
#print axioms orderedPSDSpectral_nuclear_perturbation

end NLA.Proofs.RA10
