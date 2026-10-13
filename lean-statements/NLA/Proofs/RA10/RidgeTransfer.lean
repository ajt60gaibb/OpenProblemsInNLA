import NLA.Proofs.RA10.RidgeCompression
import NLA.Proofs.RA10.RidgeTransferConditional

/-! Unconditional RA-10 transfer with constant 11 for every ridge atom.
This completes the ridge stage; the general operator-monotone Target still
requires the representation and integration stages. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Statements.RA10

namespace NLA.Proofs.RA10

/-- The full selected-approximant ridge implication, including zero tail,
singular matrices, tied eigenvalues, and every supplied ordered eigenbasis. -/
theorem ridgeTransfer_eleven {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {a b : Fin n → ℝ} {QA QB : Matrix (Fin n) (Fin n) ℝ}
    (hA : OrderedPSDSpectralDecomposition A a QA)
    (hB : OrderedPSDSpectralDecomposition Ahat b QB)
    {s ε : ℝ} (hs : 0 < s) (hε : 0 ≤ ε)
    (happrox : NuclearNorm (A - FunctionTruncation k (fun t => t) b QB) ≤
      (1 + ε) * NuclearNorm (A - FunctionTruncation k (fun t => t) a QA)) :
    NuclearNorm (FunctionMatrix (ridgeAtom s) a QA -
      FunctionTruncation k (ridgeAtom s) b QB) ≤
      (1 + 11 * ε) * NuclearNorm (FunctionMatrix (ridgeAtom s) a QA -
        FunctionTruncation k (ridgeAtom s) a QA) := by
  obtain ⟨h, QC, hC⟩ := selectedCompression_exists_orderedPSD (k := k) hA hB
  apply ridgeTransfer_of_compressionEstimate hk hkn hA hB hC hs hε _ happrox
  intro hc
  exact ridgeCompression_positivePart_trace_le (selectedProjection k QB)
    (selectedProjection_transpose k QB) (selectedProjection_idempotent hB) hA hC hs hc

#assert_trust kernel ridgeTransfer_eleven
#print axioms ridgeTransfer_eleven

end NLA.Proofs.RA10
