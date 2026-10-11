import NLA.Proofs.RA10.RidgeResolventProduct
import NLA.Proofs.RA10.SelectedProjectionIdempotent
import NLA.Proofs.RA10.CustomPSDMathlibBridge
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! RA-10 source Lemma 2, Equation (6), for a positive eigenvector of the
actual selected-compression ridge-function difference. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix

namespace NLA.Proofs.RA10

private theorem ridge_shift_mul_function {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {M : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hM : NLA.Statements.RA10.OrderedPSDSpectralDecomposition M eigenvalues Q) :
    (s • (1 : Matrix (Fin n) (Fin n) ℝ) + M) *
      NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvalues Q = M := by
  let T := s • (1 : Matrix (Fin n) (Fin n) ℝ) + M
  have hunit : IsUnit T := spectralShift_isUnit hs hM
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hunit
  have hinv : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hdet
  rw [ridgeFunctionMatrix_eq_resolvent hs hM]
  change T * (1 - s • T⁻¹) = M
  calc
    T * (1 - s • T⁻¹) = T - s • (T * T⁻¹) := by
      simp [mul_sub]
    _ = M := by rw [hinv]; dsimp [T]; module

private theorem ridge_function_eq_mul_inverse {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {M : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hM : NLA.Statements.RA10.OrderedPSDSpectralDecomposition M eigenvalues Q) :
    NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvalues Q =
      M * (s • (1 : Matrix (Fin n) (Fin n) ℝ) + M)⁻¹ := by
  let T := s • (1 : Matrix (Fin n) (Fin n) ℝ) + M
  have hunit : IsUnit T := spectralShift_isUnit hs hM
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hunit
  have hinv : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hdet
  rw [ridgeFunctionMatrix_eq_resolvent hs hM]
  change 1 - s • T⁻¹ = M * T⁻¹
  calc
    1 - s • T⁻¹ = T * T⁻¹ - s • T⁻¹ := by rw [hinv]
    _ = M * T⁻¹ := by dsimp [T]; simp [add_mul]

theorem matchedLeading_ridge_positiveEigenvector_eq6 {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC)
    {s lam : ℝ} (hs : 0 < s) (hlam : 0 < lam)
    (v : Fin n → ℝ) (hvunit : v ⬝ᵥ v = 1)
    (hZv :
      (NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC -
        NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesA QA) *ᵥ v =
        lam • v) :
    let μ := lam / (1 + lam)
    let P := selectedProjection k QAhat
    let C := P * A * P
    v ⬝ᵥ ((C - A) *ᵥ v) =
      μ * s + μ * (2 - μ) * (v ⬝ᵥ (C *ᵥ v)) := by
  let P := selectedProjection k QAhat
  let C := P * A * P
  let FA := NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesA QA
  let FC := NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC
  let x := FC *ᵥ v
  let q := 1 + lam
  let a := v ⬝ᵥ (A *ᵥ v)
  let b := v ⬝ᵥ (C *ᵥ v)
  let t := v ⬝ᵥ x
  let r := v ⬝ᵥ (A *ᵥ x)
  have hP2 : P * P = P := selectedProjection_idempotent (k := k) hAhat
  have hPt : P.transpose = P := selectedProjection_transpose k QAhat
  have hAt : A.transpose = A := by
    have hApsd := orderedPSDSpectralDecomposition_positiveSemidefinite hA
    ext i j
    exact hApsd.1 j i
  have hCt : C.transpose = C := by
    dsimp [C]
    simp only [Matrix.transpose_mul, hPt, hAt, Matrix.mul_assoc]
  have hPC : P * C = C := by
    dsimp [C]
    calc
      P * (P * A * P) = (P * P) * A * P := by simp only [Matrix.mul_assoc]
      _ = P * A * P := by rw [hP2]
  have hFA : (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A) * FA = A :=
    ridge_shift_mul_function hs hA
  have hFC : (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C) * FC = C :=
    ridge_shift_mul_function hs hC
  have hPFC : P * FC = FC := by
    have hFCfactor : FC = C * (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹ :=
      ridge_function_eq_mul_inverse hs hC
    rw [hFCfactor]
    calc
      P * (C * (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹) =
          (P * C) * (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹ := by
            exact (Matrix.mul_assoc P C _).symm
      _ = C * (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹ := by rw [hPC]
  have hPx : P *ᵥ x = x := by
    dsimp [x]
    rw [Matrix.mulVec_mulVec, hPFC]
  have hFAv : (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A) *ᵥ (FA *ᵥ v) =
      A *ᵥ v := by rw [Matrix.mulVec_mulVec, hFA]
  have hFCv : (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C) *ᵥ x =
      C *ᵥ v := by dsimp [x]; rw [Matrix.mulVec_mulVec, hFC]
  have hY : FA *ᵥ v = x - lam • v := by
    have h := hZv
    rw [Matrix.sub_mulVec] at h
    change x - FA *ᵥ v = lam • v at h
    ext i
    have hi := congrFun h i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    linarith
  have h1 : s • x + A *ᵥ x =
      q • (A *ᵥ v) + (lam * s) • v := by
    rw [hY] at hFAv
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_smul] at hFAv
    dsimp [q]
    have hh := sub_eq_iff_eq_add.mp hFAv
    simp only [smul_add, smul_smul] at hh
    calc
      s • x + A *ᵥ x = A *ᵥ v + (lam * s) • v + lam • (A *ᵥ v) := by
        simpa [add_assoc, add_comm, add_left_comm, mul_comm] using hh
      _ = (1 + lam) • (A *ᵥ v) + (lam * s) • v := by module
  have h2 : s • x + C *ᵥ x = C *ᵥ v := by
    simpa only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      using hFCv
  have hPAx : P *ᵥ (A *ᵥ x) = C *ᵥ x := by
    calc
      P *ᵥ (A *ᵥ x) = (P * A) *ᵥ x := Matrix.mulVec_mulVec x P A
      _ = (P * A) *ᵥ (P *ᵥ x) := by rw [hPx]
      _ = C *ᵥ x := by rw [Matrix.mulVec_mulVec]
  have hproj : C *ᵥ v = q • (P *ᵥ (A *ᵥ v)) + (lam * s) • (P *ᵥ v) := by
    have hp := congrArg (fun y : Fin n → ℝ => P *ᵥ y) h1
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hPx, hPAx] at hp
    exact h2.symm.trans hp
  have hPr : (P *ᵥ (A *ᵥ v)) ⬝ᵥ x = r := by
    have ht := Matrix.dotProduct_transpose_mulVec P x (A *ᵥ v)
    rw [hPt, hPx] at ht
    have ha := Matrix.dotProduct_transpose_mulVec A v x
    rw [hAt] at ha
    dsimp [r]
    calc
      (P *ᵥ (A *ᵥ v)) ⬝ᵥ x = x ⬝ᵥ (P *ᵥ (A *ᵥ v)) := dotProduct_comm _ _
      _ = (A *ᵥ v) ⬝ᵥ x := ht
      _ = x ⬝ᵥ (A *ᵥ v) := dotProduct_comm _ _
      _ = v ⬝ᵥ (A *ᵥ x) := ha.symm
  have hPtval : (P *ᵥ v) ⬝ᵥ x = t := by
    have ht := Matrix.dotProduct_transpose_mulVec P x v
    rw [hPt, hPx] at ht
    calc
      (P *ᵥ v) ⬝ᵥ x = x ⬝ᵥ (P *ᵥ v) := dotProduct_comm _ _
      _ = v ⬝ᵥ x := ht
      _ = t := rfl
  have hCval : (C *ᵥ v) ⬝ᵥ x = v ⬝ᵥ (C *ᵥ x) := by
    have ht := Matrix.dotProduct_transpose_mulVec C v x
    rw [hCt] at ht
    calc
      (C *ᵥ v) ⬝ᵥ x = x ⬝ᵥ (C *ᵥ v) := dotProduct_comm _ _
      _ = v ⬝ᵥ (C *ᵥ x) := ht.symm
  have hscalarProj : v ⬝ᵥ (C *ᵥ x) = q * r + lam * s * t := by
    have hp := congrArg (fun y : Fin n → ℝ => y ⬝ᵥ x) hproj
    simpa only [hCval, add_dotProduct, smul_dotProduct, smul_eq_mul,
      hPr, hPtval] using hp
  have hscalarC : s * t + v ⬝ᵥ (C *ᵥ x) = b := by
    have hc := congrArg (fun y : Fin n → ℝ => v ⬝ᵥ y) h2
    simpa only [dotProduct_add, dotProduct_smul, smul_eq_mul, t, b] using hc
  have hscalarA : s * t + r = q * a + lam * s := by
    have ha := congrArg (fun y : Fin n → ℝ => v ⬝ᵥ y) h1
    simpa only [dotProduct_add, dotProduct_smul, smul_eq_mul,
      t, r, a, hvunit, mul_one] using ha
  have hcore : b = q * q * a + lam * s * q := by
    have h : b = q * (s * t + r) := by
      dsimp [q] at hscalarProj ⊢
      nlinarith [hscalarProj, hscalarC]
    rw [hscalarA] at h
    nlinarith [h]
  have hq : q ≠ 0 := by dsimp [q]; linarith
  change v ⬝ᵥ ((C - A) *ᵥ v) =
    lam / q * s + lam / q * (2 - lam / q) * b
  have hdiff : v ⬝ᵥ ((C - A) *ᵥ v) = b - a := by
    simp [Matrix.sub_mulVec, dotProduct_sub, b, a]
  rw [hdiff]
  field_simp
  dsimp [q] at hcore ⊢
  nlinarith [hcore]

#assert_trust kernel matchedLeading_ridge_positiveEigenvector_eq6
#print axioms matchedLeading_ridge_positiveEigenvector_eq6

end NLA.Proofs.RA10
