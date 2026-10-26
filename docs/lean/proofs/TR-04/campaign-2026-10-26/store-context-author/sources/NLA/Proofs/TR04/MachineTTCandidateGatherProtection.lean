import NLA.Proofs.TR04.MachineTTCandidateGatherFamily
import NLA.Proofs.TR04.TTMemoryLayoutBounds

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat TensorFormat.TTStrict TTMemoryLayout

/-- All first-response/input blocks precede the literal first frame. Individual
dimension bounds suffice here; dense work capacities remain separate. -/
theorem ttCandidate_layout_saved (L : Layout) (m q l : ℕ)
    (hm : m ≤ L.entries) (hq : q ≤ L.entries) (hl : l ≤ L.entries) :
    DisjointBlocks L.firstU (m * m) L.frames (m * q) ∧
      DisjointBlocks L.firstSigma (min m l) L.frames (m * q) ∧
      DisjointBlocks L.firstV (l * l) L.frames (m * q) ∧
      DisjointBlocks L.input (m * l) L.frames (m * q) ∧ m * q ≤ L.entries ^ 2 := by
  have hu := square_capacity hm
  have hv := square_capacity hl
  have hs : min m l ≤ L.entries := (Nat.min_le_left m l).trans hm
  have hi := rectangle_capacity hm hl
  refine ⟨?_, ?_, ?_, ?_, rectangle_capacity hm hq⟩
  all_goals apply disjoint_of_end_le
  all_goals unfold Layout.frames Layout.childV Layout.childSigma Layout.firstV Layout.firstSigma Layout.firstU
  all_goals omega

/-- Complete concrete first-layout candidate endpoint: exact selected frame,
all saved first-SVD arrays and original dense input, all caller globals, and
uniform quadratic actual charge. The subsequent child replies are unrestricted. -/
theorem ttCandidateGather_protected {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 189) (hs : s.status = .running)
    {B : Matrix (Fin (s.natural 81)) (Fin (s.natural 82)) ℝ}
    {U : Matrix (Fin (s.natural 81)) (Fin (s.natural 81)) ℝ}
    {sigma : Fin (min (s.natural 81) (s.natural 82)) → ℝ}
    {V : Matrix (Fin (s.natural 82)) (Fin (s.natural 82)) ℝ}
    (hvalid : ValidSVD B U sigma V) (hr : 1 ≤ s.natural 80)
    (hcap : s.natural 106 = min (s.natural 80) (min (s.natural 81) (s.natural 82)))
    (hselected : TTFirstSelected (ttFirstChoice sigma hvalid.2.2.2.1 (s.natural 80)
      (min (s.natural 80) (min (s.natural 81) (s.natural 82))) hr) s)
    (hj : s.natural 76 < s.natural 75)
    (hU : StoresFrame s.memory (s.natural 72) (s.natural 81) U)
    (hsigma : ∀ k, s.memory (s.natural 73 + k.val) = sigma k)
    (hV : readMatrix s.memory (s.natural 82) (s.natural 82) (s.natural 74) = V)
    (L : Layout) (hrows : s.natural 81 ≤ L.entries) (hwidth : s.natural 106 ≤ L.entries)
    (hcols : s.natural 82 ≤ L.entries)
    (hUbase : s.natural 72 = L.firstU) (hSbase : s.natural 73 = L.firstSigma)
    (hVbase : s.natural 74 = L.firstV) (hFbase : s.natural 67 = L.frames)
    (hIbase : s.natural 92 = L.input) :
    let F := explicitFirstFrames hvalid (s.natural 80)
    let time := s.natural 81 * (11 * s.natural 106 + 7) + 24
    let n := offset + time
    ∃ j : Fin F.count, j.val = s.natural 76 ∧ s.natural 106 = F.width ∧
      time ≤ 24 * (L.entries + 1)^2 ∧
      (trace.state n).label = 241 ∧ (trace.state n).status = .running ∧
      StoresFrame (trace.state n).memory (s.natural 67) F.width (F.frame j) ∧
      readMatrix (trace.state n).memory (s.natural 81) (s.natural 82) (s.natural 92) =
        readMatrix s.memory (s.natural 81) (s.natural 82) (s.natural 92) ∧
      readMatrix (trace.state n).memory (s.natural 81) (s.natural 81) (s.natural 72) = U ∧
      (∀ k, (trace.state n).memory (s.natural 73 + k.val) = sigma k) ∧
      readMatrix (trace.state n).memory (s.natural 82) (s.natural 82) (s.natural 74) = V ∧
      (∀ a, ¬(s.natural 67 ≤ a ∧ a < s.natural 67 + s.natural 81 * s.natural 106) →
        (trace.state n).memory a = s.memory a) ∧
      TTCandidateMetadataFields s (trace.state n) ∧
      (trace.state n).natural 85 ≤ L.entries ∧ (trace.state n).natural 86 ≤ L.entries ∧
      (trace.state n).natural 87 ≤ L.entries ∧ (trace.state n).natural 88 ≤ L.entries ∧
      (∀ k : Fin 128, TTCandidateProtectedNat k → (trace.state n).natural k = s.natural k) ∧
      (∀ k : Fin 16, k ≠ 6 → (trace.state n).real k = s.real k) ∧
      CostThrough ttProgram trace n ≤ CostThrough ttProgram trace offset + 24 * (L.entries + 1)^2 := by
  obtain ⟨hdU, hdS, hdV, hdI, _⟩ := ttCandidate_layout_saved L (s.natural 81) (s.natural 106)
    (s.natural 82) hrows hwidth hcols
  rw [←hUbase, ←hFbase] at hdU
  rw [←hSbase, ←hFbase] at hdS
  rw [←hVbase, ←hFbase] at hdV
  rw [←hIbase, ←hFbase] at hdI
  obtain ⟨j, hjval, hq, hlabel, hrun, hframe, _, hout, hfields, hnat, hreal, hcost⟩ :=
    ttCandidateGather_explicit ht offset s he hl hs hvalid hr hcap hselected hj hU hdU
  have hbound := ttCandidateGather_time_le_quadratic (s.natural 81) (s.natural 106) L.entries hrows hwidth
  have hread (base rows cols : ℕ)
      (hd : DisjointBlocks base (rows * cols) (s.natural 67) (s.natural 81 * s.natural 106)) :
      readMatrix (trace.state (offset + (s.natural 81 * (11 * s.natural 106 + 7) + 24))).memory rows cols base =
        readMatrix s.memory rows cols base := by
    ext i k
    exact hout _ (disjointBlocks_not_mem_right hd (by have hh := matrix_offset_lt i k; omega))
  refine ⟨j, hjval, hq, hbound, hlabel, hrun, hframe, hread _ _ _ hdI, ?_, ?_, ?_, hout,
    hfields, hfields.rows.trans_le hrows, hfields.width.trans_le hwidth,
    hfields.cols.trans_le hcols, hfields.stride.trans_le hwidth, hnat, hreal,
    hcost.trans (Nat.add_le_add_left hbound _)⟩
  · exact (hread _ _ _ hdU).trans ((storesFrame_dense_iff _ _ U).mp hU)
  · intro k
    exact (hout _ (disjointBlocks_not_mem_right hdS (by have hh := k.isLt; omega))).trans (hsigma k)
  · exact (hread _ _ _ hdV).trans hV

#assert_trust kernel ttCandidate_layout_saved
#assert_trust kernel ttCandidateGather_protected
#print axioms ttCandidateGather_protected
end NLA.Proofs.TR04
