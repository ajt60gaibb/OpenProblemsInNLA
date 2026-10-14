import NLA.Proofs.RA10.LoewnerAtomTransfer
import NLA.Proofs.RA10.SpectralIntegral

/-! Full constant-11 transfer for functions with a finite positive harmonic
representation. Measure existence is a premise of this internal assembly;
`OperatorMonotoneRepresentation` proves and discharges it. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open MeasureTheory NLA.Statements.RA10

namespace NLA.Proofs.RA10

/-- All integration and endpoint cases of the transfer are discharged here.
No positive-tail assumption is needed, and selected zero eigenvalues are retained. -/
theorem compactLoewnerTransfer_eleven {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {a b : Fin n → ℝ} {QA QB : Matrix (Fin n) (Fin n) ℝ}
    (hA : OrderedPSDSpectralDecomposition A a QA)
    (hB : OrderedPSDSpectralDecomposition Ahat b QB)
    {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : NuclearNorm (A - FunctionTruncation k (fun x => x) b QB) ≤
      (1 + ε) * NuclearNorm (A - FunctionTruncation k (fun x => x) a QA))
    {f : ℝ → ℝ} (hf : HasCompactLoewnerRepresentation f) :
    NuclearNorm (FunctionMatrix f a QA - FunctionTruncation k f b QB) ≤
      (1 + 11 * ε) * NuclearNorm (FunctionMatrix f a QA - FunctionTruncation k f a QA) := by
  obtain ⟨μ, hμ, hrep⟩ := hf
  let : IsFiniteMeasure μ := hμ
  have ha (i : Fin n) : Integrable (fun t => loewnerAtom t (a i)) μ :=
    loewnerAtom_integrable μ (hA.1 i)
  have hb (i : Fin n) : Integrable (fun t => loewnerAtom t (b i)) μ :=
    loewnerAtom_integrable μ (hB.1 i)
  have hfa : FunctionMatrix f a QA =
      fun i j => ∫ t, FunctionMatrix (loewnerAtom t) a QA i j ∂μ := by
    rw [functionMatrix_congr (g := fun x => ∫ t, loewnerAtom t x ∂μ)
      a QA (fun i => hrep (a i) (hA.1 i))]
    exact functionMatrix_integral μ loewnerAtom a QA ha
  have hfb : FunctionTruncation k f b QB =
      fun i j => ∫ t, FunctionTruncation k (loewnerAtom t) b QB i j ∂μ := by
    rw [functionTruncation_congr k (g := fun x => ∫ t, loewnerAtom t x ∂μ)
      b QB (fun i => hrep (b i) (hB.1 i))]
    exact functionTruncation_integral μ k loewnerAtom b QB hb
  let M : LoewnerParameter → Matrix (Fin n) (Fin n) ℝ := fun t =>
    FunctionMatrix (loewnerAtom t) a QA - FunctionTruncation k (loewnerAtom t) b QB
  have hMint (i j : Fin n) : Integrable (fun t => M t i j) μ :=
    (functionMatrix_entry_integrable μ loewnerAtom a QA ha i j).sub
      (functionTruncation_entry_integrable μ k loewnerAtom b QB hb i j)
  have herr : FunctionMatrix f a QA - FunctionTruncation k f b QB =
      fun i j => ∫ t, M t i j ∂μ := by
    rw [hfa, hfb]
    ext i j
    exact (integral_sub (functionMatrix_entry_integrable μ loewnerAtom a QA ha i j)
      (functionTruncation_entry_integrable μ k loewnerAtom b QB hb i j)).symm
  let τ : LoewnerParameter → ℝ := fun t => ∑ i : Fin n,
    if k ≤ i.val then loewnerAtom t (a i) else 0
  have hτterm (i : Fin n) :
      Integrable (fun t => if k ≤ i.val then loewnerAtom t (a i) else 0) μ := by
    by_cases hi : k ≤ i.val
    · simpa [hi] using ha i
    · simp only [if_neg hi]
      exact integrable_zero _ _ _
  have hτ : Integrable τ μ := integrable_finsetSum _ fun i _ => hτterm i
  have hfnn (i : Fin n) : 0 ≤ f (a i) := by
    rw [hrep (a i) (hA.1 i)]
    exact integral_nonneg fun t => loewnerAtom_nonneg t (hA.1 i)
  have htail : (∫ t, τ t ∂μ) =
      NuclearNorm (FunctionMatrix f a QA - FunctionTruncation k f a QA) := by
    rw [nuclearNorm_functionMatrix_sub_truncation f a QA hA.2.2.1 hfnn]
    change (∫ t, ∑ i : Fin n, if k ≤ i.val then loewnerAtom t (a i) else 0 ∂μ) = _
    rw [integral_finsetSum _ (fun i _ => hτterm i)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : k ≤ i.val <;> simp [hi, ← hrep (a i) (hA.1 i)]
  have hbound (t : LoewnerParameter) : NuclearNorm (M t) ≤ (1 + 11 * ε) * τ t := by
    have h := loewnerAtomTransfer_eleven hk hkn hA hB hε happrox t
    rw [nuclearNorm_functionMatrix_sub_truncation (loewnerAtom t) a QA hA.2.2.1
      (fun i => loewnerAtom_nonneg t (hA.1 i))] at h
    exact h
  rw [herr]
  calc
    _ ≤ ∫ t, (1 + 11 * ε) * τ t ∂μ :=
      nuclearNorm_integral_le μ M _ hMint (hτ.const_mul _) hbound
    _ = _ := by rw [integral_const_mul, htail]

/-- Internal assembly from representation existence. The unconditional caller
is `transferBound_eleven` in `OperatorMonotoneRepresentation`. -/
theorem transferBound_eleven_of_compactLoewnerRepresentation
    (hrep : ∀ f : ℝ → ℝ, AdmissibleFunction f → HasCompactLoewnerRepresentation f) :
    TransferBound 11 := by
  intro n k _hn hk hkn A Ahat a b QA QB hA hB ε hε f hf happrox
  exact compactLoewnerTransfer_eleven hk hkn hA hB hε happrox (hrep f hf)

theorem target_of_compactLoewnerRepresentation
    (hrep : ∀ f : ℝ → ℝ, AdmissibleFunction f → HasCompactLoewnerRepresentation f) :
    Target :=
  ⟨11, by norm_num, transferBound_eleven_of_compactLoewnerRepresentation hrep⟩

#assert_trust kernel compactLoewnerTransfer_eleven
#assert_trust kernel transferBound_eleven_of_compactLoewnerRepresentation
#assert_trust kernel target_of_compactLoewnerRepresentation
#print axioms compactLoewnerTransfer_eleven
#print axioms target_of_compactLoewnerRepresentation

end NLA.Proofs.RA10
