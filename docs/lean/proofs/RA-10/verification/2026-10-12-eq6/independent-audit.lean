import NLA.Proofs.RA10.RidgeCompressionEq6Eigenvector

set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix
open NLA.Proofs.RA10

example {n k : ℕ}
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
      μ * s + μ * (2 - μ) * (v ⬝ᵥ (C *ᵥ v)) :=
  matchedLeading_ridge_positiveEigenvector_eq6
    hk hkn hA hAhat hC hs hlam v hvunit hZv

#assert_trust kernel matchedLeading_ridge_positiveEigenvector_eq6
#print axioms matchedLeading_ridge_positiveEigenvector_eq6
