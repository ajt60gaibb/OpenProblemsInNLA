import Target
import DualWitness

open Matrix

namespace MD01Scratch

private def allOnes (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun _ _ => 1

private theorem allOnes_psd (n : ℕ) : (allOnes n).PosSemidef := by
  convert (Matrix.posSemidef_vecMulVec_self_star
    (fun _ : Fin n => (1 : ℝ))) using 1
  ext i j
  simp [allOnes, Matrix.vecMulVec]

private theorem psd_sum_nonneg {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosSemidef) : 0 ≤ ∑ i, ∑ j, W i j := by
  simpa [dotProduct, Matrix.mulVec] using
    (hW.dotProduct_mulVec_nonneg (fun _ : Fin n => (1 : ℝ)))

/-- A rescaled target witness for G constructs a trace-one feasible SDP
matrix for the complement, with value at least n/(1+1/a). -/
theorem complement_lower_of_rescaled_witness {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (W : Matrix (Fin n) (Fin n) ℝ)
    (a : ℝ) (ha : 0 < a)
    (hW : W.PosSemidef)
    (hdiag : ∀ i, W i i = 1)
    (hnonedge : ∀ i j, i ≠ j → ¬ G.Adj i j → W i j = -a) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X.PosSemidef ∧ X.trace = 1 ∧
      (∀ i j, Gᶜ.Adj i j → X i j = 0) ∧
      (n : ℝ) / (1 + 1 / a) ≤ ∑ i, ∑ j, X i j := by
  classical
  let s : ℝ := 1 / a
  let lam : ℝ := 1 + s
  let J : Matrix (Fin n) (Fin n) ℝ := allOnes n
  let B : Matrix (Fin n) (Fin n) ℝ := J + s • W
  let den : ℝ := (n : ℝ) * lam
  let X : Matrix (Fin n) (Fin n) ℝ := den⁻¹ • B
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hden : 0 < den := by dsimp [den]; positivity
  have hBpsd : B.PosSemidef := (allOnes_psd n).add (hW.smul hs)
  have hBdiag (i : Fin n) : B i i = lam := by
    simp [B, J, allOnes, hdiag i, lam, s]
  have hBnonedge (i j : Fin n) (hij : i ≠ j) (hijG : ¬ G.Adj i j) :
      B i j = 0 := by
    simp [B, J, allOnes, hnonedge i j hij hijG, s]
    field_simp
    norm_num
  have hBtrace : B.trace = den := by
    simp [Matrix.trace, hBdiag, den, Finset.sum_const, nsmul_eq_mul]
  have hBsum : (n : ℝ)^2 ≤ ∑ i, ∑ j, B i j := by
    have hWsum := psd_sum_nonneg hW
    have hsumid : (∑ i, ∑ j, B i j) =
        (n : ℝ)^2 + s * (∑ i, ∑ j, W i j) := by
      simp [B, J, allOnes, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hsumid]
    nlinarith [mul_nonneg hs hWsum]
  have hXpsd : X.PosSemidef := hBpsd.smul (by positivity : 0 ≤ den⁻¹)
  have hXtrace : X.trace = 1 := by
    simp [X, Matrix.trace_smul, hBtrace, ne_of_gt hden]
  have hXedge (i j : Fin n) (hij : Gᶜ.Adj i j) : X i j = 0 := by
    have hne : i ≠ j := Gᶜ.ne_of_adj hij
    have hpair : i ≠ j ∧ ¬ G.Adj i j := by simpa using hij
    have hnot : ¬ G.Adj i j := hpair.2
    simp [X, hBnonedge i j hne hnot]
  refine ⟨X, hXpsd, hXtrace, hXedge, ?_⟩
  have hXsumid : (∑ i, ∑ j, X i j) = den⁻¹ * (∑ i, ∑ j, B i j) := by
    simp [X, ← Finset.mul_sum]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase : (n : ℝ) / lam = den⁻¹ * (n : ℝ)^2 := by
    dsimp [den]
    field_simp
  calc
    (n : ℝ) / (1 + 1 / a) = (n : ℝ) / lam := rfl
    _ = den⁻¹ * (n : ℝ)^2 := hbase
    _ ≤ den⁻¹ * (∑ i, ∑ j, B i j) :=
      mul_le_mul_of_nonneg_left hBsum (inv_nonneg.mpr (le_of_lt hden))
    _ = ∑ i, ∑ j, X i j := hXsumid.symm

/-- The explicit witness also gives a lower bound on theta of the complement. -/
theorem theta_complement_lower_of_rescaled_witness {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (W : Matrix (Fin n) (Fin n) ℝ)
    (a : ℝ) (ha : 0 < a)
    (hW : W.PosSemidef)
    (hdiag : ∀ i, W i i = 1)
    (hnonedge : ∀ i j, i ≠ j → ¬ G.Adj i j → W i j = -a) :
    (n : ℝ) / (1 + 1 / a) ≤ theta Gᶜ := by
  obtain ⟨X, hX, htr, hedge, hvalue⟩ :=
    complement_lower_of_rescaled_witness hn G W a ha hW hdiag hnonedge
  have hmem : (∑ i, ∑ j, X i j) ∈
      {v : ℝ | ∃ Y : Matrix (Fin n) (Fin n) ℝ,
        Y.PosSemidef ∧ Y.trace = 1 ∧
        (∀ i j, Gᶜ.Adj i j → Y i j = 0) ∧
        v = ∑ i, ∑ j, Y i j} := ⟨X, hX, htr, hedge, rfl⟩
  exact hvalue.trans (le_csSup (theta_domain_bddAbove n Gᶜ) hmem)

/-- Appendix A's primal lower-bound construction applied to a Definition 2.5
target matrix. -/
theorem theta_complement_lower_of_target_matrix {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (R : Matrix (Fin n) (Fin n) ℝ)
    (a : ℝ) (ha : 0 < a)
    (hRdiag : ∀ i, R i i = 0)
    (hRnonedge : ∀ i j, ¬ G.Adj i j → R i j = 0)
    (hW : ((1 : Matrix (Fin n) (Fin n) ℝ) +
      a • MD01Dual.signedAdj G + R).PosSemidef) :
    (n : ℝ) / (1 + 1 / a) ≤ theta Gᶜ := by
  classical
  apply theta_complement_lower_of_rescaled_witness hn G
    (1 + a • MD01Dual.signedAdj G + R) a ha hW
  · intro i
    simp [MD01Dual.signedAdj, hRdiag i]
  · intro i j hij hnon
    simp [MD01Dual.signedAdj, hij, hnon, hRnonedge i j hnon]

#print axioms MD01Scratch.allOnes_psd
#print axioms MD01Scratch.psd_sum_nonneg
#print axioms MD01Scratch.complement_lower_of_rescaled_witness
#print axioms MD01Scratch.theta_complement_lower_of_rescaled_witness
#print axioms MD01Scratch.theta_complement_lower_of_target_matrix

end MD01Scratch
