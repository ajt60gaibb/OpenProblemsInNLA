import NLA.TR13.Compression
import NLA.TR13.Koszul
import NLA.TR13.MatrixCertificate

/-!
The compressed Koszul flattening acts on the full ambient tensor space.
Its rank bound therefore applies to arbitrary ordinary decompositions and to
arbitrary entrywise convergent ordinary border decompositions.
-/

noncomputable section
open scoped BigOperators
open Filter Matrix

namespace NLA.TR13

/-- Reversing the first compressed coordinate normalizes the explicit spike
witness. It remains a fixed coordinate map on all ambient tensors. -/
def compressedSlices (k n : ℕ) (hn : 0 < n) (T : Tensor (2 * k + 1) n) :
    ThreeSlices (k * (n - 1) + 1) :=
  fun j u v => compressedTensor k n hn T u.rev j v

def tensorKoszul (k n : ℕ) (hn : 0 < n) (T : Tensor (2 * k + 1) n) :
    Matrix (KoszulIndex (k * (n - 1) + 1)) (KoszulIndex (k * (n - 1) + 1)) ℂ :=
  koszul (compressedSlices k n hn T)

theorem compressedSlices_sum (k n : ℕ) (hn : 0 < n) {ι : Type*}
    (s : Finset ι) (T : ι → Tensor (2 * k + 1) n) :
    compressedSlices k n hn (∑ i ∈ s, T i) =
      ∑ i ∈ s, compressedSlices k n hn (T i) := by
  ext j u v
  simp [compressedSlices, compressedTensor, Finset.sum_apply, Matrix.sum_apply]

theorem tensorKoszul_sum (k n : ℕ) (hn : 0 < n) {ι : Type*}
    (s : Finset ι) (T : ι → Tensor (2 * k + 1) n) :
    tensorKoszul k n hn (∑ i ∈ s, T i) =
      ∑ i ∈ s, tensorKoszul k n hn (T i) := by
  simp only [tensorKoszul, compressedSlices_sum, koszul_sum]

theorem tensorKoszul_pure_rank_le (k n : ℕ) (hn : 0 < n)
    (v : Fin (2 * k + 1) → Fin n → ℂ) :
    (tensorKoszul k n hn (pureTensor v)).rank ≤ 2 := by
  obtain ⟨c, u, w, h⟩ := compressedTensor_pure k n hn v
  have hs : compressedSlices k n hn (pureTensor v) =
      fun j x y => c j * u x.rev * w y := by
    funext j x y
    exact h x.rev j y
  rw [tensorKoszul, hs]
  exact koszul_pure_rank_le (fun x => u x.rev) w c

theorem tensorKoszul_rank_le_of_ordinary (k n : ℕ) (hn : 0 < n)
    {q : ℕ} {T : Tensor (2 * k + 1) n} (hT : OrdinaryRankAtMost q T) :
    (tensorKoszul k n hn T).rank ≤ 2 * q := by
  obtain ⟨v, rfl⟩ := hT
  rw [tensorKoszul_sum]
  calc
    (∑ i : Fin q, tensorKoszul k n hn (pureTensor (v i))).rank
        ≤ ∑ i : Fin q, (tensorKoszul k n hn (pureTensor (v i))).rank :=
      matrix_rank_sum_le _
    _ ≤ ∑ _i : Fin q, 2 :=
      Finset.sum_le_sum fun i _ => tensorKoszul_pure_rank_le k n hn (v i)
    _ = 2 * q := by simp [Nat.mul_comm]

theorem continuous_compressedSlices (k n : ℕ) (hn : 0 < n) :
    Continuous (compressedSlices k n hn) := by
  unfold compressedSlices compressedTensor
  fun_prop

theorem continuous_tensorKoszul (k n : ℕ) (hn : 0 < n) :
    Continuous (tensorKoszul k n hn) :=
  (continuous_koszul _).comp (continuous_compressedSlices k n hn)

theorem tensorKoszul_rank_le_of_ordinaryBorder (k n : ℕ) (hn : 0 < n)
    {q : ℕ} {T : Tensor (2 * k + 1) n} (hT : OrdinaryBorderRankAtMost q T) :
    (tensorKoszul k n hn T).rank ≤ 2 * q := by
  obtain ⟨U, hU, hlim⟩ := hT
  apply matrix_rank_le_of_tendsto (fun i => tensorKoszul k n hn (U i))
    (tensorKoszul k n hn T)
  · exact (continuous_tensorKoszul k n hn).continuousAt.tendsto.comp hlim
  · intro i
    exact tensorKoszul_rank_le_of_ordinary k n hn (hU i)

/-- The moment coordinate selected by a reversed compressed slice. -/
def compressedMomentIndex (k n : ℕ) (hn : 0 < n) (j : Fin 3)
    (u v : Fin (k * (n - 1) + 1)) : Fin ((2 * k + 1) * (n - 1) + 1) :=
  ⟨u.rev.val + j.val * ((n - 1) / 2) + v.val, by
    have hu := u.rev.isLt
    have hv := v.isLt
    have hj := (middleIndex n hn j).isLt
    change j.val * ((n - 1) / 2) < n at hj
    have hnn : n - 1 + 1 = n := by omega
    nlinarith⟩

theorem tensorKoszul_hankel (k n : ℕ) (hn : 0 < n)
    (h : Moments (2 * k + 1) n) :
    tensorKoszul k n hn (hankel h) =
      koszul (fun j u v => h (compressedMomentIndex k n hn j u v)) := by
  unfold tensorKoszul
  congr 1
  funext j u v
  exact compressedTensor_hankel k n hn h u.rev v j

/-- Polynomial matrix whose specialization is the full tensor Koszul
flattening restricted to Hankel parameters. -/
def hankelKoszulPolynomial (k n : ℕ) (hn : 0 < n) :
    Matrix (KoszulIndex (k * (n - 1) + 1)) (KoszulIndex (k * (n - 1) + 1))
      (MvPolynomial (Fin ((2 * k + 1) * (n - 1) + 1)) ℂ) :=
  koszul (fun j u v => MvPolynomial.X (compressedMomentIndex k n hn j u v))

theorem hankelKoszulPolynomial_eval (k n : ℕ) (hn : 0 < n)
    (h : Moments (2 * k + 1) n) :
    (hankelKoszulPolynomial k n hn).map (MvPolynomial.eval h) =
      tensorKoszul k n hn (hankel h) := by
  rw [tensorKoszul_hankel]
  ext ⟨i, u⟩ ⟨j, v⟩
  fin_cases i <;> fin_cases j <;> simp [hankelKoszulPolynomial, koszul]

/-- One high-rank Hankel witness gives an ordinary-border lower bound on a
nonempty principal open set. Nonemptiness follows separately from `p ≠ 0`
over the infinite field of complex numbers. -/
theorem exists_lower_polynomial_of_witness (k n r : ℕ) (hn : 0 < n)
    (hw : ∃ h : Moments (2 * k + 1) n,
      2 * r ≤ (tensorKoszul k n hn (hankel h)).rank) :
    ∃ p : MvPolynomial (Fin ((2 * k + 1) * (n - 1) + 1)) ℂ,
      p ≠ 0 ∧ ∀ h ∈ principalOpen p, ∀ q,
        OrdinaryBorderRankAtMost q (hankel h) → r ≤ q := by
  obtain ⟨h0, h0rank⟩ := hw
  have h0p : 2 * r ≤
      ((hankelKoszulPolynomial k n hn).map (MvPolynomial.eval h0)).rank := by
    simpa only [hankelKoszulPolynomial_eval] using h0rank
  obtain ⟨p, hp, _, hcert⟩ :=
    exists_polynomial_rank_certificate (hankelKoszulPolynomial k n hn) h0 h0p
  refine ⟨p, hp, ?_⟩
  intro h hh q hq
  have hlow := hcert h hh
  rw [hankelKoszulPolynomial_eval] at hlow
  have hupp := tensorKoszul_rank_le_of_ordinaryBorder k n hn hq
  omega

end NLA.TR13
