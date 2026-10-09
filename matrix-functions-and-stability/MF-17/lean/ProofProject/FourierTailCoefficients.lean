import ProofProject.TailGeometry

/-!
# Nonnegative scalar frequencies give coefficient tails

The vector polynomial has frequencies `-j`. At output frequency `q`, cutting
the scalar polynomial to nonnegative frequencies retains precisely `q+j ≥ 0`.
The corresponding zero-based tail starts at `(-q).toNat`.
-/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

lemma fourierTail_coefficients (v : Fin n → H) (c : ℤ → ℂ) (q : ℤ) :
    finiteSynthesis v (fun j => if 0 ≤ q + (j.val : ℤ) then c (q + j.val) else 0) =
      synthesisTail v (fun j => c (q + j.val)) (-q).toNat := by
  unfold finiteSynthesis synthesisTail
  apply Finset.sum_congr rfl
  intro j _
  have hj : 0 ≤ q + (j.val : ℤ) ↔ (-q).toNat ≤ j.val := by omega
  by_cases h : 0 ≤ q + (j.val : ℤ)
  · simp only [if_pos h, if_pos (hj.mp h)]
  · have hnot : ¬(-q).toNat ≤ j.val := fun hle => h (hj.mpr hle)
    simp only [if_neg h, if_neg hnot, zero_smul]

/-- Finite coefficient energy contracts under nonnegative scalar truncation.
Full and empty output tails are included; no frequency-range assumptions are
needed for this finite sum. -/
theorem fourierTail_energy_le {v : Fin n → H} {K : ℝ}
    (h : HasSynthesisTailBound v K) (s : Finset ℤ) (c : ℤ → ℂ) :
    (∑ q ∈ s, ‖finiteSynthesis v
      (fun j => if 0 ≤ q + (j.val : ℤ) then c (q + j.val) else 0)‖ ^ 2) ≤
      K ^ 2 * ∑ q ∈ s, ‖finiteSynthesis v (fun j => c (q + j.val))‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  rw [fourierTail_coefficients]
  simpa only [mul_pow] using
    pow_le_pow_left₀ (norm_nonneg _) (h (fun j => c (q + j.val)) (-q).toNat) 2

end ProofProject
