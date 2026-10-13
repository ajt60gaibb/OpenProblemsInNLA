import NLA.Proofs.RA10.SpectralFunctionOperations
import NLA.Proofs.RA10.OperatorMonotonePositiveApproximation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-! Independence of the supplied spectral basis, and a bridge to Mathlib's
functional calculus. No ordering or positivity is required for independence;
in particular repeated eigenvalues cause no extra hypothesis. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Matrix
open scoped BigOperators
open NLA.Statements.RA10

namespace NLA.Proofs.RA10

theorem functionMatrix_basis_independent {n : ℕ} (f : ℝ → ℝ)
    {a b : Fin n → ℝ} {Q R : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.transpose * Q = 1) (hR : R.transpose * R = 1)
    (h : SpectralMatrix a Q = SpectralMatrix b R) :
    FunctionMatrix f a Q = FunctionMatrix f b R := by
  have hQQ := mul_eq_one_comm.mp hQ
  have hRR := mul_eq_one_comm.mp hR
  have hinter : diagonal a * (Q.transpose * R) = (Q.transpose * R) * diagonal b := by
    have hh := congrArg (fun M => Q.transpose * M * R) h
    simpa only [spectralMatrix_factor, Matrix.mul_assoc, ← Matrix.mul_assoc Q.transpose Q,
      hQ, one_mul, ← Matrix.mul_assoc R.transpose R, hR, mul_one] using hh
  have hfinter : diagonal (fun i => f (a i)) * (Q.transpose * R) =
      (Q.transpose * R) * diagonal (fun i => f (b i)) := by
    ext i j
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hinter
    simp only [diagonal_mul, mul_diagonal] at hij ⊢
    by_cases hab : a i = b j
    · rw [hab, mul_comm]
    · have hz : (Q.transpose * R) i j = 0 := by
        have hm : (a i - b j) * (Q.transpose * R) i j = 0 := by nlinarith [hij]
        exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hab)
      simp [hz]
  have hh := congrArg (fun M => Q * M * R.transpose) hfinter
  simpa only [FunctionMatrix, spectralMatrix_factor, Matrix.mul_assoc,
    ← Matrix.mul_assoc R R.transpose, hRR, mul_one,
    ← Matrix.mul_assoc Q Q.transpose, hQQ, one_mul] using hh

theorem functionMatrix_eq_cfc {n : ℕ} (f : ℝ → ℝ)
    {A : Matrix (Fin n) (Fin n) ℝ} {a : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.transpose * Q = 1) (hA : A = SpectralMatrix a Q) :
    FunctionMatrix f a Q = cfc f A := by
  have hherm : A.IsHermitian := by
    rw [hA, spectralMatrix_factor]
    apply Matrix.isHermitian_iff_isSymm.mpr
    simp [Matrix.IsSymm, Matrix.transpose_mul, Matrix.mul_assoc]
  let U : Matrix (Fin n) (Fin n) ℝ := hherm.eigenvectorUnitary
  have hU : U.transpose * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self hherm.eigenvectorUnitary
  have heq : A = SpectralMatrix hherm.eigenvalues U := by
    simpa only [spectralMatrix_factor, U, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      Function.comp_def, RCLike.ofReal_real_eq_id, id_eq]
      using hherm.spectral_theorem
  rw [functionMatrix_basis_independent f hQ hU (hA.symm.trans heq), hherm.cfc_eq]
  simp only [FunctionMatrix, spectralMatrix_factor, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial, U, Function.comp_def, RCLike.ofReal_real_eq_id,
    id_eq]

theorem orderedPSD_functionMatrix_eq_cfc {n : ℕ} (f : ℝ → ℝ)
    {A : Matrix (Fin n) (Fin n) ℝ} {a : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hA : OrderedPSDSpectralDecomposition A a Q) :
    FunctionMatrix f a Q = cfc f A := by
  apply functionMatrix_eq_cfc f _ hA.2.2.2
  ext i j
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hA.2.2.1 i j

theorem orderedPSD_eigenvalues_pos_of_posDef {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {a : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hA : OrderedPSDSpectralDecomposition A a Q) (hpos : A.PosDef) : ∀ i, 0 < a i := by
  have hQ : Q.transpose * Q = 1 := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hA.2.2.1 i j
  have hu : IsUnit Q := isUnit_iff_exists_inv.mpr ⟨Q.transpose, mul_eq_one_comm.mp hQ⟩
  have hd : (diagonal a).PosDef := by
    apply hu.posDef_star_right_conjugate_iff.mp
    simpa only [hA.2.2.2, spectralMatrix_factor, Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] using hpos
  exact posDef_diagonal_iff.mp hd

theorem operatorMonotoneOnPositive_cfc {n : ℕ} {f : ℝ → ℝ}
    (hf : OperatorMonotoneOnPositive f)
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : (A - B).PosSemidef) : (cfc f A - cfc f B).PosSemidef := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz : cfc f A - cfc f B = 0 := Subsingleton.elim _ _
    rw [hz]
    exact PosSemidef.zero
  obtain ⟨a, Q, ha⟩ := mathlibPosSemidef_exists_orderedPSD hA.posSemidef
  obtain ⟨b, R, hb⟩ := mathlibPosSemidef_exists_orderedPSD hB.posSemidef
  rw [← orderedPSD_functionMatrix_eq_cfc f ha, ← orderedPSD_functionMatrix_eq_cfc f hb]
  exact (sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mp
    (hf n hn A B a b Q R (orderedPSD_eigenvalues_pos_of_posDef ha hA)
      (orderedPSD_eigenvalues_pos_of_posDef hb hB) ha hb
      ((sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mpr hAB))

#assert_trust kernel functionMatrix_basis_independent
#assert_trust kernel functionMatrix_eq_cfc
#assert_trust kernel orderedPSD_functionMatrix_eq_cfc
#assert_trust kernel orderedPSD_eigenvalues_pos_of_posDef
#assert_trust kernel operatorMonotoneOnPositive_cfc
#print axioms operatorMonotoneOnPositive_cfc

end NLA.Proofs.RA10
