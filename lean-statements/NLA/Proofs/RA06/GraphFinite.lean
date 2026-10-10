import NLA.Proofs.RA06.GraphWitness

/-! Finite support and expected-size consequences of the graph witness. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RA06

open NLA.Statements.RA06

/-- In the dimension regime where the accuracy threshold is the smaller
branch, the handshake identity converts the per-vertex obstruction into a
uniform graph-support lower bound. -/
theorem positiveEdgeCount_lower_of_approx {v : ℕ}
    (p ε : ℝ) (hp : 1 < p) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hv : 1 < v) (w : Edge v → ℝ) (hw : ∀ e, 0 ≤ w e)
    (happrox : ∀ z : Fin v → ℝ,
      (1 - ε) * CompleteEnergy p z ≤ WeightedEnergy p w z ∧
      WeightedEnergy p w z ≤ (1 + ε) * CompleteEnergy p z)
    (hregime : Real.rpow (6 * ε) (-p) ≤ ((v - 1 : ℕ) : ℝ) * ε) :
    (v : ℝ) * Real.rpow (6 * ε) (-p) ≤
      2 * (PositiveEdgeCount w : ℝ) := by
  apply positiveEdgeCount_lower_of_all_degrees w
  intro u
  rcases supportDegree_lower_of_approx p ε hp hε hεhalf hv w hw happrox u with
    hlarge | hlarge
  · exact hregime.trans hlarge
  · exact hlarge

/-- The exact matrix sample retains as many rows as its positive weighted
graph has edges. Every successful all-vector sample therefore obeys the
finite support lower bound. -/
theorem successful_retainedCount_lower
    (d : ℕ) (hd : 0 < d) (p ε α : ℝ)
    (hp : 1 < p) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hα : 0 < α)
    (hregime : Real.rpow (6 * ε) (-p) ≤ (d : ℝ) * ε)
    (kept : Fin (Fintype.card (Edge (d + 1))) → Bool)
    (hemb : Embedding (GraphMatrix d) p α ε kept) :
    (((d + 1 : ℕ) : ℝ) / 2) * Real.rpow (6 * ε) (-p) ≤
      (RetainedCount kept : ℝ) := by
  let w := SampleWeight d p α kept
  have hv : 1 < d + 1 := by omega
  have hbound := positiveEdgeCount_lower_of_approx p ε hp hε hεhalf hv
    w (sampleWeight_nonneg d hd p α hα kept)
    (embedding_to_weighted d p α ε kept hemb) hregime
  rw [sample_positiveEdgeCount_eq_retainedCount d hd p α hα kept] at hbound
  nlinarith

/-- The `1-δ` success mass remains explicit in the expected-size lower
bound; it is not replaced by existence of one successful outcome. -/
theorem expectedSize_lower_from_graph_success
    (d : ℕ) (hd : 0 < d) (p ε δ α : ℝ)
    (hp : 1 < p) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hα : 0 < α)
    (hregime : Real.rpow (6 * ε) (-p) ≤ (d : ℝ) * ε)
    (hsuccess : 1 - δ ≤
      SuccessProbability (GraphMatrix d) p α ε) :
    (1 - δ) *
      ((((d + 1 : ℕ) : ℝ) / 2) * Real.rpow (6 * ε) (-p)) ≤
      ExpectedSize (GraphMatrix d) p α := by
  let L : ℝ := (((d + 1 : ℕ) : ℝ) / 2) * Real.rpow (6 * ε) (-p)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hn := graphMatrix_rows_pos d hd
  have htransfer := expectedSize_lower_of_success_count_bound
    (GraphMatrix d) p α ε L (graphMatrix_fullColumnRank d) hn hd hα
    (fun kept hemb => successful_retainedCount_lower d hd p ε α
      hp hε hεhalf hα hregime kept hemb)
  exact (mul_le_mul_of_nonneg_right hsuccess hL).trans htransfer

#print axioms positiveEdgeCount_lower_of_approx
#print axioms successful_retainedCount_lower
#print axioms expectedSize_lower_from_graph_success

end NLA.Proofs.RA06
