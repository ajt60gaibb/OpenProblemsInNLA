import Problem56.PaperV7.Certification

open Problem56 Problem56.PaperV6 Problem56.PaperV7

/-- Independent reviewer client: direct prescribed-width probability statement,
with the spectral-supremum and public Reference wrappers eliminated. -/
theorem reviewer_prescribed_squared_norm_success
    (m r : ℕ) (ε : ℝ) (hr : 1 ≤ r) (hrn : r ≤ walshCard m)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : V.transpose * V = 1) :
    let k := min (walshCard m)
      (Nat.ceil ((explicitUniversalConstant : ℝ) * r / ε ^ 2))
    (99 : ℝ) / 100 ≤ uniformProbability
      (fun sample : SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
          FixedSubset (WalshIndex m) k ↦
        ∀ x : Fin r → ℝ,
          (1 - ε) * euclideanNorm (V.mulVec x) ^ 2 ≤
            euclideanNorm ((rerandomizedSRHT sample.1 sample.2.1 sample.2.2).transpose.mulVec
              (V.mulVec x)) ^ 2 ∧
          euclideanNorm ((rerandomizedSRHT sample.1 sample.2.1 sample.2.2).transpose.mulVec
              (V.mulVec x)) ^ 2 ≤ (1 + ε) * euclideanNorm (V.mulVec x) ^ 2) := by
  let k := prescribedWidth m r ε
  have hk : k ≤ walshCard m :=
    (prescribedWidth_bounds m r ε hr hrn ⟨hε0, hε1⟩).2
  letI := fixedSubset_nonempty k hk
  have hs := certified_explicit_main.2 m r ε hr hrn hε0 hε1
  have hf : frameFailureProbability (k := k) ε V ≤ 1 / 100 :=
    (frameFailureProbability_le_sup ε V hV).trans hs
  change (99 : ℝ) / 100 ≤ uniformProbability
    (fun sample : SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
      FixedSubset (WalshIndex m) k ↦ SquaredNormEdges ε V sample.1 sample.2.1 sample.2.2)
  have hevent :
      (fun sample : SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
        FixedSubset (WalshIndex m) k ↦ SquaredNormEdges ε V sample.1 sample.2.1 sample.2.2) =
      (fun sample ↦ ¬ euclideanOperatorNorm
        (compressedGram V sample.1 sample.2.1 sample.2.2 - 1) > ε) := by
    funext sample
    apply propext
    rw [squared_edges_iff_spectral_bound ε hε0.le V hV, not_lt]
  rw [hevent, uniformProbability_complement]
  unfold frameFailureProbability at hf
  linarith

example (m : ℕ) : walshCard m = 2 ^ m := I01_walsh_card m

#print axioms reviewer_prescribed_squared_norm_success
#print axioms Problem56.PaperV7.certified_main
#print axioms Problem56.PaperV7.certified_explicit_main
#print axioms Problem56.PaperV7.main_prescribed_width_ose
