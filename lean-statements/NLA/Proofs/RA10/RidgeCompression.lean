import NLA.Proofs.RA10.RidgeCompressionQuadratic
import NLA.Proofs.RA10.PositivePartTraceBound

/-! RA-10 source Lemma 2, including singular compressions. The proof uses
positive shifts, the energy equations, and summation of quadratic bounds over
a full orthonormal basis. No regularisation or limit is required. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Matrix
open NLA.Statements.RA10
open scoped BigOperators

namespace NLA.Proofs.RA10

/-- The full ridge compression estimate for any orthogonal projection P. -/
theorem ridgeCompression_positivePart_trace_le {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.transpose = P) (hPP : P * P = P)
    {a h : Fin n → ℝ} {QA QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : OrderedPSDSpectralDecomposition A a QA)
    (hC : OrderedPSDSpectralDecomposition (P * A * P) h QC)
    {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    Matrix.trace (hermitianPositivePart
      (FunctionMatrix (ridgeAtom s) h QC - FunctionMatrix (ridgeAtom s) a QA)) ≤
      2 / (s + c) * (Matrix.trace (hermitianPositivePart (P * A * P - A)) +
        Matrix.trace (hermitianPositivePart (c • P - P * A * P))) := by
  let C := P * A * P
  let Z := FunctionMatrix (ridgeAtom s) h QC - FunctionMatrix (ridgeAtom s) a QA
  let T := hermitianPositivePart (C - A) + hermitianPositivePart (c • P - C)
  have hApsd := (sourcePositiveSemidefinite_iff_mathlibPosSemidef A).mp
    (orderedPSDSpectralDecomposition_positiveSemidefinite hA)
  have hCpsd := (sourcePositiveSemidefinite_iff_mathlibPosSemidef C).mp
    (orderedPSDSpectralDecomposition_positiveSemidefinite hC)
  have hZ : Z.IsHermitian :=
    (ridgeFunctionMatrix_posSemidef hC hs).1.sub (ridgeFunctionMatrix_posSemidef hA hs).1
  have hD : (C - A).IsHermitian := hCpsd.1.sub hApsd.1
  have hM : (c • P - C).IsHermitian :=
    ((Matrix.isHermitian_iff_isSymm.mpr hP).smul (by rfl)).sub hCpsd.1
  have hT : T.PosSemidef :=
    (hermitianPositivePart_posSemidef (C - A) hD).add
      (hermitianPositivePart_posSemidef (c • P - C) hM)
  have hsc : 0 < s + c := add_pos hs hc
  have hscaled : ((2 / (s + c)) • T).PosSemidef := hT.smul (by positivity)
  have htrace := hermitianPositivePart_trace_le_of_eigenvector_bound Z
    ((2 / (s + c)) • T) hZ hscaled (by
      intro i hi
      let v : Fin n → ℝ := fun j => hZ.eigenvectorUnitary j i
      have hUtU : (hZ.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).transpose *
          (hZ.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) = 1 := by
        simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
          using Unitary.coe_star_mul_self hZ.eigenvectorUnitary
      have hv : v ⬝ᵥ v = 1 := by
        have hdiag := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i) hUtU
        simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
          dotProduct, v] using hdiag
      have heig : Z *ᵥ v = hZ.eigenvalues i • v := hZ.mulVec_eigenvectorBasis i
      have hpoint := ridgeCompression_eigenvector_bound P hP hPP hA hC hs hc hi v hv heig
      change hZ.eigenvalues i ≤ v ⬝ᵥ (((2 / (s + c)) • T) *ᵥ v)
      simp only [smul_mulVec, dotProduct_smul, smul_eq_mul]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hsc).mpr
      change hZ.eigenvalues i * (s + c) / 2 ≤ v ⬝ᵥ (T *ᵥ v) at hpoint
      linarith)
  simpa only [Matrix.trace_smul, smul_eq_mul, T, Matrix.trace_add] using htrace

#assert_trust kernel ridgeCompression_positivePart_trace_le
#print axioms ridgeCompression_positivePart_trace_le

end NLA.Proofs.RA10
