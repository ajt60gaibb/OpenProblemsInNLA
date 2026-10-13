import NLA.Proofs.RA10.CompactLoewnerKernel
import NLA.Proofs.RA10.SpectralFunctionOperations
import NLA.Proofs.RA10.RidgeTransfer

/-! Constant, linear, and harmonic atoms all satisfy the same RA-10 bound. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open NLA.Statements.RA10

namespace NLA.Proofs.RA10

/-- A constant function has the same selected error in either supplied basis,
even when the selected eigenvalues vanish. -/
theorem constantFunction_selected_error {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ} {a b : Fin n → ℝ}
    {QA QB : Matrix (Fin n) (Fin n) ℝ}
    (hA : OrderedPSDSpectralDecomposition A a QA)
    (hB : OrderedPSDSpectralDecomposition Ahat b QB) :
    NuclearNorm (FunctionMatrix (fun _ => 1) a QA - FunctionTruncation k (fun _ => 1) b QB) =
      NuclearNorm (FunctionMatrix (fun _ => 1) a QA - FunctionTruncation k (fun _ => 1) a QA) := by
  have hid : FunctionMatrix (fun _ => 1) a QA = FunctionMatrix (fun _ => 1) b QB := by
    rw [functionMatrix_const 1 a QA hA.2.2.1, functionMatrix_const 1 b QB hB.2.2.1]
  rw [hid, nuclearNorm_functionMatrix_sub_truncation (fun _ => 1) b QB hB.2.2.1
    (fun _ => by norm_num), ← hid]
  rw [nuclearNorm_functionMatrix_sub_truncation (fun _ => 1) a QA hA.2.2.1
    (fun _ => by norm_num)]

theorem loewnerAtomTransfer_eleven {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {a b : Fin n → ℝ} {QA QB : Matrix (Fin n) (Fin n) ℝ}
    (hA : OrderedPSDSpectralDecomposition A a QA)
    (hB : OrderedPSDSpectralDecomposition Ahat b QB)
    {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : NuclearNorm (A - FunctionTruncation k (fun x => x) b QB) ≤
      (1 + ε) * NuclearNorm (A - FunctionTruncation k (fun x => x) a QA))
    (t : LoewnerParameter) :
    NuclearNorm (FunctionMatrix (loewnerAtom t) a QA - FunctionTruncation k (loewnerAtom t) b QB) ≤
      (1 + 11 * ε) * NuclearNorm
        (FunctionMatrix (loewnerAtom t) a QA - FunctionTruncation k (loewnerAtom t) a QA) := by
  by_cases ht0 : (t : ℝ) = 0
  · have hfun : loewnerAtom t = fun _ => 1 := by funext x; simp [loewnerAtom, ht0]
    rw [hfun, constantFunction_selected_error hA hB]
    nlinarith [nuclearNorm_nonneg
      (FunctionMatrix (fun _ => 1) a QA - FunctionTruncation k (fun _ => 1) a QA)]
  by_cases ht1 : (t : ℝ) = 1
  · have hfun : loewnerAtom t = fun x => x := by funext x; simp [loewnerAtom, ht1]
    have hid : FunctionMatrix (fun x => x) a QA = A := hA.2.2.2.symm
    rw [hfun, hid]
    exact happrox.trans (mul_le_mul_of_nonneg_right (by linarith)
      (nuclearNorm_nonneg _))
  have ht0pos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht0)
  have ht1lt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 ht1
  have hs : 0 < (t : ℝ) / (1 - (t : ℝ)) := div_pos ht0pos (sub_pos.mpr ht1lt)
  have hc : 0 ≤ (1 - (t : ℝ))⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr t.property.2)
  have hfun : loewnerAtom t = fun x =>
      (1 - (t : ℝ))⁻¹ * ridgeAtom ((t : ℝ) / (1 - (t : ℝ))) x :=
    funext (loewnerAtom_eq_scaled_ridge t ht0pos ht1lt)
  rw [hfun, functionMatrix_smul, functionTruncation_smul, functionTruncation_smul,
    ← smul_sub, ← smul_sub, nuclearNorm_smul, nuclearNorm_smul, abs_of_nonneg hc]
  have h := mul_le_mul_of_nonneg_left (ridgeTransfer_eleven hk hkn hA hB hs hε happrox) hc
  simpa only [mul_left_comm, mul_assoc] using h

#assert_trust kernel constantFunction_selected_error
#assert_trust kernel loewnerAtomTransfer_eleven
#print axioms loewnerAtomTransfer_eleven

end NLA.Proofs.RA10
