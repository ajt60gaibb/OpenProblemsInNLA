import NLA.Statements.RE05

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery

/-- A fixed absolute asymptotic bound for the literal manuscript count. -/
theorem sourceQueryBound_numeric (q : ℕ) (ε : ℝ) (hpos : 0 < ε)
    (hsmall : ε < 1 / 2) :
    15 * (2 * Real.sqrt ((q + 1 : ℕ) * baseWidth q (squaredAccuracy ε)) +
      8 * Real.log (20 * (q + 1 : ℕ)) + 1) ≤
    1000000 * Real.sqrt (q + 1 : ℕ) * ε⁻¹ *
      (1 + Real.log (2 + (q + 1 : ℕ)) + Real.log (1 / ε)) := by
  let N : ℝ := (q + 1 : ℕ)
  let E : ℝ := ε⁻¹
  let L : ℝ := 1 + Real.log (2 + N) + Real.log (1 / ε)
  let B : ℝ := baseWidth q (squaredAccuracy ε)
  have hN : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (show 1 ≤ q + 1 by omega)
  have hE : 1 ≤ E := (one_le_inv₀ hpos).mpr (by linarith)
  have hlogN : 0 ≤ Real.log (2 + N) := Real.log_nonneg (by linarith)
  have hlogE : 0 ≤ Real.log (1 / ε) := by
    simpa only [one_div] using Real.log_nonneg hE
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hlog : Real.log (20 * N) ≤ 20 * L := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have h20 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 20 by norm_num)
    have hmon := Real.log_le_log (show 0 < N by linarith) (show N ≤ 2 + N by linarith)
    dsimp [L]
    linarith
  have hlog0 : 0 ≤ Real.log (20 * N) := Real.log_nonneg (by linarith)
  have hB : B = 16 * Real.log (20 * N) + 1440 * E := by
    dsimp [B, baseWidth, squaredAccuracy, N, E]
    field_simp; ring
  have hLE : L ≤ L * E := by nlinarith
  have hBE : B ≤ 1760 * (L * E) := by rw [hB]; nlinarith
  have hB1 : 1 ≤ B := by rw [hB]; nlinarith
  have hsqrtB : Real.sqrt B ≤ 1760 * (L * E) :=
    (Real.sqrt_le_self_iff.mpr (Or.inr hB1)).trans hBE
  have hsqrtN : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN
  have hproduct : L * E ≤ Real.sqrt N * (L * E) := by
    exact le_mul_of_one_le_left (by positivity) hsqrtN
  have hmain : Real.sqrt (N * B) ≤ 1760 * (Real.sqrt N * (L * E)) := by
    rw [Real.sqrt_mul (by linarith : 0 ≤ N)]
    calc
      Real.sqrt N * Real.sqrt B ≤ Real.sqrt N * (1760 * (L * E)) :=
        mul_le_mul_of_nonneg_left hsqrtB (Real.sqrt_nonneg N)
      _ = 1760 * (Real.sqrt N * (L * E)) := by ring
  have hrest : 8 * Real.log (20 * N) + 1 ≤
      161 * (Real.sqrt N * (L * E)) := by nlinarith
  have hfinal :
      15 * (2 * Real.sqrt (N * B) + 8 * Real.log (20 * N) + 1) ≤
        1000000 * Real.sqrt N * E * L := by nlinarith
  simpa only [N, B, E, L, one_div] using hfinal

/-- The unchanged concrete source bound implies the literal original
asymptotic query companion with fixed constants, for every random stream.
The source bound remains a named intermediate premise of this bridge. -/
theorem queryBound_of_sourceQueryBound {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (hpos : 0 < ε) (hsmall : ε < 1 / 2)
    (hsource : NLA.Statements.RE05.SourceQueryBound P ε) :
    NLA.Statements.RE05.QueryBound P ε 1000000 1 1 := by
  intro ω
  simpa only [pow_one] using (hsource ω).trans (sourceQueryBound_numeric q ε hpos hsmall)

#assert_trust kernel sourceQueryBound_numeric
#assert_trust kernel queryBound_of_sourceQueryBound
#print axioms sourceQueryBound_numeric
#print axioms queryBound_of_sourceQueryBound
end NLA.Proofs.RE05
