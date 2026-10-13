import NLA.Proofs.RA10.RidgeShiftInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-! RA-10 exact ridge resolvent identity for the frozen functional calculus.
No commutation of the two PSD matrices or their supplied eigenbases is used.
The matrix compression/nuclear transfer estimates remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

private theorem spectralMatrix_sub_smul {n : ℕ}
    (u v : Fin n → ℝ) (s : ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.SpectralMatrix (fun a => u a - s * v a) Q =
      NLA.Statements.RA10.SpectralMatrix u Q -
        s • NLA.Statements.RA10.SpectralMatrix v Q := by
  ext i j
  simp only [NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    (∑ a : Fin n, (u a - s * v a) * Q i a * Q j a) =
        ∑ a : Fin n, (u a * Q i a * Q j a - s * (v a * Q i a * Q j a)) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (∑ a : Fin n, u a * Q i a * Q j a) -
          s * (∑ a : Fin n, v a * Q i a * Q j a) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]

theorem ridgeFunctionMatrix_eq_resolvent {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q) :
    NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvalues Q =
      1 - s • (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹ := by
  rcases h with ⟨hvalues, horder, hQ, hA⟩
  have hdecomp : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      A eigenvalues Q := ⟨hvalues, horder, hQ, hA⟩
  have hQTQ : Q.transpose * Q = 1 := by
    ext a b
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hQ a b
  have hQQT : Q * Q.transpose = 1 := mul_eq_one_comm.mp hQTQ
  have hconst : NLA.Statements.RA10.FunctionMatrix (fun _ => (1 : ℝ)) eigenvalues Q =
      1 := by
    ext i j
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hQQT
    simpa [NLA.Statements.RA10.FunctionMatrix,
      NLA.Statements.RA10.SpectralMatrix, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.one_apply] using hij
  have hscalar (a : Fin n) :
      ridgeAtom s (eigenvalues a) =
        1 - s * (1 / (s + eigenvalues a)) := by
    have hpos : 0 < s + eigenvalues a := by linarith [hvalues a]
    unfold ridgeAtom
    field_simp
    ring
  have hweighted : NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvalues Q =
      NLA.Statements.RA10.FunctionMatrix (fun _ => (1 : ℝ)) eigenvalues Q -
        s • NLA.Statements.RA10.FunctionMatrix
          (fun x => 1 / (s + x)) eigenvalues Q := by
    change NLA.Statements.RA10.SpectralMatrix
        (fun a => ridgeAtom s (eigenvalues a)) Q = _
    simp_rw [hscalar]
    exact spectralMatrix_sub_smul (fun _ => 1)
      (fun a => 1 / (s + eigenvalues a)) s Q
  calc
    NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvalues Q =
        NLA.Statements.RA10.FunctionMatrix (fun _ => (1 : ℝ)) eigenvalues Q -
          s • NLA.Statements.RA10.FunctionMatrix
            (fun x => 1 / (s + x)) eigenvalues Q := hweighted
    _ = 1 - s • (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹ := by
      rw [hconst, spectralShift_inverse hs hdecomp]

theorem ridgeFunctionMatrix_sub {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A C : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesC : Fin n → ℝ}
    {QA QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition C eigenvaluesC QC) :
    NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC -
      NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesA QA =
      s • ((s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹ -
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹) := by
  rw [ridgeFunctionMatrix_eq_resolvent hs hC,
    ridgeFunctionMatrix_eq_resolvent hs hA]
  module

#assert_trust kernel ridgeFunctionMatrix_eq_resolvent
#assert_trust kernel ridgeFunctionMatrix_sub
#print axioms ridgeFunctionMatrix_sub

end NLA.Proofs.RA10
