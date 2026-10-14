import NLA.Proofs.RA10.SelectedApproximantPerturbation
import NLA.Proofs.RA10.MatchedLeadingEq8
import NLA.Proofs.RA10.MatchedLeadingEq9
import NLA.Proofs.RA10.MatchedLeadingEq10
import NLA.Proofs.RA10.MatchedLeadingEq11Variational
import NLA.Proofs.RA10.MatchedLeadingEq12RidgeLoss
import NLA.Proofs.RA10.MatchedLeadingEq13TraceIdentity
import NLA.Proofs.RA10.NuclearIdealEq14Restricted
import NLA.Proofs.RA10.ConstantElevenArithmetic

/-! Conditional RA-10 ridge transfer: the exact source Lemma 2 estimate is
an explicit hypothesis. All subsequent matrix estimates and the constant 11
are proved here. This is not a proof of Lemma 2, TransferBound, or Target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open NLA.Statements.RA10

namespace NLA.Proofs.RA10

theorem nuclearNorm_sub_comm {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ) :
    NuclearNorm (X - Y) = NuclearNorm (Y - X) := by
  have h : X - Y = (-1 : ℝ) • (Y - X) := by
    ext i j
    simp
  rw [h, nuclearNorm_smul]
  norm_num

/-- With zero optimal tail, the approximation premise forces exact ridge recovery.
This lemma has no compression hypothesis. -/
theorem ridge_selected_error_zero_of_zeroTail {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {a b : Fin n → ℝ} {QA QB : Matrix (Fin n) (Fin n) ℝ}
    (hA : OrderedPSDSpectralDecomposition A a QA)
    (hB : OrderedPSDSpectralDecomposition Ahat b QB)
    {s ε : ℝ} (hs : 0 < s)
    (hτ : (∑ i : Fin n, if k ≤ i.val then a i else 0) = 0)
    (happrox : NuclearNorm (A - FunctionTruncation k (fun t => t) b QB) ≤
      (1 + ε) * NuclearNorm (A - FunctionTruncation k (fun t => t) a QA)) :
    NuclearNorm (FunctionMatrix (ridgeAtom s) a QA -
      FunctionTruncation k (ridgeAtom s) b QB) = 0 := by
  rw [nuclearNorm_orderedPSD_tail hA, hτ, mul_zero] at happrox
  have hmatrix : A = FunctionTruncation k (fun t => t) b QB :=
    sub_eq_zero.mp ((nuclearNorm_eq_zero_iff _).mp
      (le_antisymm happrox (nuclearNorm_nonneg _)))
  have hfunction : FunctionMatrix (ridgeAtom s) a QA =
      FunctionTruncation k (ridgeAtom s) b QB := by
    rw [ridgeFunctionMatrix_eq_resolvent hs hA,
      ← matchedLeading_ridgeFunctionMatrix hs b QB,
      ridgeFunctionMatrix_eq_resolvent hs (matchedLeading_orderedPSD (k := k) hB hB),
      hmatrix]
  rw [hfunction, sub_self]
  exact (nuclearNorm_eq_zero_iff _).mpr rfl

/-- Source (8)–(21), including zero tail, conditional only on the stated
positive-cutoff compression estimate. The supplied basis of Ahat is retained. -/
theorem ridgeTransfer_of_compressionEstimate {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {a b h : Fin n → ℝ} {QA QB QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : OrderedPSDSpectralDecomposition A a QA)
    (hB : OrderedPSDSpectralDecomposition Ahat b QB)
    (hC : OrderedPSDSpectralDecomposition
      (selectedProjection k QB * A * selectedProjection k QB) h QC)
    {s ε : ℝ} (hs : 0 < s) (hε : 0 ≤ ε)
    (hcompression : 0 < a ⟨k - 1, by omega⟩ →
      Matrix.trace (hermitianPositivePart
        (FunctionMatrix (ridgeAtom s) h QC - FunctionMatrix (ridgeAtom s) a QA)) ≤
      2 / (s + a ⟨k - 1, by omega⟩) *
        (Matrix.trace (hermitianPositivePart
          (selectedProjection k QB * A * selectedProjection k QB - A)) +
        Matrix.trace (hermitianPositivePart
          (a ⟨k - 1, by omega⟩ • selectedProjection k QB -
            selectedProjection k QB * A * selectedProjection k QB))))
    (happrox : NuclearNorm (A - FunctionTruncation k (fun t => t) b QB) ≤
      (1 + ε) * NuclearNorm (A - FunctionTruncation k (fun t => t) a QA)) :
    NuclearNorm (FunctionMatrix (ridgeAtom s) a QA -
      FunctionTruncation k (ridgeAtom s) b QB) ≤
      (1 + 11 * ε) * NuclearNorm (FunctionMatrix (ridgeAtom s) a QA -
        FunctionTruncation k (ridgeAtom s) a QA) := by
  by_cases hτ : (∑ i : Fin n, if k ≤ i.val then a i else 0) = 0
  · rw [ridge_selected_error_zero_of_zeroTail hA hB hs hτ happrox]
    exact mul_nonneg (by linarith) (nuclearNorm_nonneg _)
  have hτpos : 0 < ∑ i : Fin n, if k ≤ i.val then a i else 0 :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => by split_ifs <;> simp_all only [hA.1 i, le_refl]))
      (Ne.symm hτ)
  have hc := orderedPSD_cutoff_pos_of_tail_pos hk hkn hA hτpos
  specialize hcompression hc
  rw [nuclearNorm_orderedPSD_tail hA] at happrox
  rw [nuclearNorm_functionMatrix_sub_truncation (ridgeAtom s) a QA hA.2.2.1
    (fun i => div_nonneg (hA.1 i) (le_of_lt (add_pos_of_pos_of_nonneg hs (hA.1 i))))]
  let c := a ⟨k - 1, by omega⟩
  let g := 1 / (s + c)
  let C := selectedProjection k QB * A * selectedProjection k QB
  let B := FunctionTruncation k (fun t : ℝ => t) b QB
  let B₀ := FunctionTruncation k (fun t : ℝ => t) a QB
  let F_A := FunctionMatrix (ridgeAtom s) a QA
  let F_C := FunctionMatrix (ridgeAtom s) h QC
  let F_B := FunctionTruncation k (ridgeAtom s) b QB
  let F₀ := FunctionTruncation k (ridgeAtom s) a QB
  let τ := ∑ i : Fin n, if k ≤ i.val then a i else 0
  let τs := ∑ i : Fin n, if k ≤ i.val then ridgeAtom s (a i) else 0
  let e := NuclearNorm (A - B) - τ
  let e₀ := NuclearNorm (A - B₀) - τ
  let eC := NuclearNorm (A - C) - τ
  let r := ∑ i : Fin n, if i.val < k then |a i - b i| else 0
  let R := NuclearNorm (B₀ - C)
  let L := (∑ i : Fin n, if i.val < k then a i else 0) - Matrix.trace C
  let Ls := (∑ i : Fin n, if i.val < k then ridgeAtom s (a i) else 0) -
    Matrix.trace F_C
  let t := Matrix.trace (hermitianPositivePart (C - A))
  let d := Matrix.trace (hermitianPositivePart (c • selectedProjection k QB - C))
  let ts := Matrix.trace (hermitianPositivePart (F_C - F_A))
  have hg : 0 ≤ g := le_of_lt (one_div_pos.mpr (add_pos hs hc))
  have h8 : R + L ≤ e₀ := matchedLeading_excess_ge_remainder_plus_loss hk hkn hA hB
  have h9 : eC ≤ e₀ + R := matchedLeading_compression_excess_le hk hkn hA hB
  have h10 : eC = L + 2 * t :=
    matchedLeading_compression_excess_positivePart hk hkn hA hB
  have h11 : d ≤ L := matchedLeading_defect_le_loss hk hkn hA hB
  have h12 : Ls ≤ g * L := by
    simpa only [g, div_eq_mul_inv, one_mul, mul_one, mul_comm] using
      (matchedLeading_ridge_loss_nonneg_le hk hkn hA hB hC hs hc).2
  have h13 : NuclearNorm (F_A - F_C) - τs = Ls + 2 * ts :=
    matchedLeading_ridge_excess_positivePart_identity hk hkn hA hB hC hs hc
  have h14 : NuclearNorm (F_C - F₀) ≤ g * R := by
    rw [nuclearNorm_sub_comm F_C F₀]
    exact matchedLeading_ridge_nuclear_le hs hk hkn hA hB hC
      ⟨k - 1, by omega⟩ (by simp only; omega)
  have hcomp : ts ≤ 2 * g * (t + d) := by
    simpa only [g, div_eq_mul_inv, one_mul] using hcompression
  have hscaled11 := mul_le_mul_of_nonneg_left h11 hg
  have hscaled8 := mul_le_mul_of_nonneg_left h8 hg
  have hscaled9 := mul_le_mul_of_nonneg_left h9 hg
  have hcompressed : NuclearNorm (F_A - F_C) - τs ≤ g * (2 * eC + 3 * L) := by
    nlinarith [hcomp]
  have htriangle₀ : NuclearNorm (F_A - F₀) ≤
      NuclearNorm (F_A - F_C) + NuclearNorm (F_C - F₀) := by
    have heq : F_A - F₀ = (F_A - F_C) + (F_C - F₀) := by abel
    rw [heq]
    exact nuclearNorm_add_le _ _
  have h15 : NuclearNorm (F_A - F₀) - τs ≤ 5 * g * e₀ := by
    nlinarith
  have h16 : r ≤ e := selectedApproximant_spectral_error_le_excess hA hB
  have h17 : e₀ ≤ e + r := selectedApproximant_matched_excess_le hB
  have h18 : NuclearNorm (F₀ - F_B) ≤ g * r := by
    simpa only [g, div_eq_mul_inv, one_mul, mul_one, mul_comm] using
      selectedApproximant_ridge_difference_le hk hkn hA hB hs hc
  have htriangle : NuclearNorm (F_A - F_B) ≤
      NuclearNorm (F_A - F₀) + NuclearNorm (F₀ - F_B) := by
    have heq : F_A - F_B = (F_A - F₀) + (F₀ - F_B) := by abel
    rw [heq]
    exact nuclearNorm_add_le _ _
  have h19 : NuclearNorm (F_A - F_B) - τs ≤ 11 * g * e :=
    ridgeExcess_le_eleven hg h16 h17 (by linarith)
  have h20 : g * τ ≤ τs := by
    have htail := ridgeAtom_tail_sum_lower (k := k) a hs hc hA.1
      (fun i hi => hA.2.1 (by
        apply Fin.le_iff_val_le_val.mpr
        change k - 1 ≤ i.val
        omega))
    simpa only [Finset.sum_filter, g, div_eq_mul_inv, one_mul, mul_one, mul_comm] using htail
  have he : e ≤ ε * τ := by
    change NuclearNorm (A - B) ≤ (1 + ε) * τ at happrox
    dsimp [e]
    linarith
  exact ridgeTransfer_of_excess hg hε h19 he h20

#assert_trust kernel nuclearNorm_sub_comm
#assert_trust kernel ridge_selected_error_zero_of_zeroTail
#assert_trust kernel ridgeTransfer_of_compressionEstimate
#print axioms ridge_selected_error_zero_of_zeroTail
#print axioms ridgeTransfer_of_compressionEstimate

end NLA.Proofs.RA10
