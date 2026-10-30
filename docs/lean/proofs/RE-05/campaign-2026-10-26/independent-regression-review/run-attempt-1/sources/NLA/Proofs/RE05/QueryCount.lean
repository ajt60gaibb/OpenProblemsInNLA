import NLA.Statements.RE05

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.NonadaptiveMatrixQuery

/-- Actual known-family selected-column count; it depends on no random draw
or unknown target response. -/
def selectedCount {n q : ℕ} (P : Basis n q) (ε : ℝ) : ℕ :=
  ((List.finRange n).filter fun j => threshold q (squaredAccuracy ε) <
    (exactSVD (leverage P)).sigma (Fin.cast (Nat.min_self n).symm j)).length

/-- Exact charged length of the actual fifteen-copy committed query batch. -/
theorem batchQueries_length {n q : ℕ} (P : Basis n q) (ε : ℝ) (ω : ℕ → ℝ) :
    (batchQueries (plans P ε ω)).length =
      15 * (selectedCount P ε + gaussianWidth q (squaredAccuracy ε)) := by
  simp [batchQueries, plans, queries, NLA.Computation.LinearFamilyQuery.makePlan, selectedCount, List.length_flatMap,
    ]
  omega

/-- The actual source width and threshold are positive at every allowed accuracy. -/
theorem baseWidth_positive (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    0 < baseWidth q (squaredAccuracy ε) := by
  have h20 : (1 : ℝ) < 20 * (q + 1 : ℕ) := by
    exact_mod_cast (show 1 < 20 * (q + 1) by omega)
  have hl := Real.log_pos h20
  unfold baseWidth squaredAccuracy
  positivity

/-- The exact threshold/width balance, with no rounding approximation. -/
theorem threshold_mul_width (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    threshold q (squaredAccuracy ε) * baseWidth q (squaredAccuracy ε) =
      Real.sqrt ((q + 1 : ℕ) * baseWidth q (squaredAccuracy ε)) := by
  let B := baseWidth q (squaredAccuracy ε)
  let N : ℝ := (q + 1 : ℕ)
  have hB : 0 < B := baseWidth_positive q ε hε
  have hN : 0 ≤ N := by positivity
  have ht : 0 ≤ threshold q (squaredAccuracy ε) := Real.sqrt_nonneg _
  have hs : threshold q (squaredAccuracy ε) ^ 2 = N / B :=
    Real.sq_sqrt (div_nonneg hN hB.le)
  apply (sq_eq_sq₀ (mul_nonneg ht hB.le) (Real.sqrt_nonneg _)).mp
  rw [mul_pow, hs, Real.sq_sqrt (mul_nonneg hN hB.le)]
  change N / B * B ^ 2 = N * B
  field_simp

/-- A selected-column spectral charge yields exactly the manuscript's actual
query-count companion. This is a named bridge: the charge itself is a separate
linear-algebra proof obligation, never a premise of any claimed full Target. -/
theorem sourceQueryBound_of_selected_charge {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (hε : 0 < ε)
    (hcharge : (selectedCount P ε : ℝ) * threshold q (squaredAccuracy ε) ≤
      (q + 1 : ℕ)) : NLA.Statements.RE05.SourceQueryBound P ε := by
  let B := baseWidth q (squaredAccuracy ε)
  let N : ℝ := (q + 1 : ℕ)
  let t := threshold q (squaredAccuracy ε)
  let z := Real.sqrt (N * B)
  have hB : 0 < B := baseWidth_positive q ε hε
  have hN : 0 < N := by positivity
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hN hB)
  have htz : t * B = z := threshold_mul_width q ε hε
  have hNz : N = t * z := by
    rw [← htz]
    have hs : t ^ 2 = N / B := Real.sq_sqrt (div_nonneg hN.le hB.le)
    calc
      N = (N / B) * B := (div_mul_cancel₀ N (ne_of_gt hB)).symm
      _ = t * (t * B) := by rw [← hs]; ring
  have hK : (selectedCount P ε : ℝ) ≤ z := by
    apply (mul_le_mul_iff_right₀ ht).mp
    have hc : (selectedCount P ε : ℝ) * t ≤ N := hcharge
    rw [hNz] at hc
    simpa only [mul_comm] using hc
  have hl : 0 < Real.log (20 * (q + 1 : ℕ)) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < 20 * (q + 1) by omega)
  have hs : (gaussianWidth q (squaredAccuracy ε) : ℝ) ≤
      8 * Real.log (20 * (q + 1 : ℕ)) + z + 1 := by
    have hn : 0 ≤ 8 * Real.log (20 * (q + 1 : ℕ)) + t * B := by positivity
    have hc := (Nat.ceil_lt_add_one hn).le
    simpa only [gaussianWidth, ← htz] using hc
  intro ω
  have hbound : 15 * ((selectedCount P ε : ℝ) +
      (gaussianWidth q (squaredAccuracy ε) : ℝ)) ≤
    15 * (2 * z + 8 * Real.log (20 * (q + 1 : ℕ)) + 1) := by
    nlinarith
  simpa only [batchQueries_length, z, N, B, Nat.cast_mul, Nat.cast_add,
    Nat.cast_ofNat, Nat.cast_one] using hbound

#assert_trust kernel batchQueries_length
#assert_trust kernel baseWidth_positive
#assert_trust kernel threshold_mul_width
#assert_trust kernel sourceQueryBound_of_selected_charge
#print axioms sourceQueryBound_of_selected_charge
end NLA.Proofs.RE05
