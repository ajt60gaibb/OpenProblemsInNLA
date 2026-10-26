import NLA.Proofs.TR04.MachineTTFirstSelectionSVD
import NLA.Proofs.TR04.MachineFrameGatherSVD

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine
open TensorFormat.TTStrict

def ttFirstGatherParameters (m : ℕ) (C : TTFirstChoice) (j inputBase outputBase : ℕ) : FrameGatherParameters :=
  ⟨m, C.above, C.tied, C.take, j, inputBase, outputBase⟩

/-- Literal finite-gather columns realize the exact frozen explicit family.
The only index transports preserve natural values. -/
def TTFirstChoiceRealizes {m r : ℕ} (U : Matrix (Fin m) (Fin m) ℝ)
    (C : TTFirstChoice) (F : FirstFrames m r) (inputBase outputBase : ℕ) : Prop :=
  ∃ hc : C.count = F.count, ∃ hw : C.above + C.take = F.width,
    ∀ j : Fin C.count,
      ∃ hP : (ttFirstGatherParameters m C j.val inputBase outputBase).Valid,
        (frameGatherMatrix (ttFirstGatherParameters m C j.val inputBase outputBase) hP U).submatrix
          id (Fin.cast hw.symm) = F.frame (Fin.cast hc j)

theorem ttFirstPrefix_realizes {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (r inputBase outputBase : ℕ) :
    TTFirstChoiceRealizes U (ttFirstPrefixChoice (min r (min m l))) (defaultFrames h r)
      inputBase outputBase := by
  refine ⟨rfl, rfl, ?_⟩
  intro j
  have hj : j.val = 0 := by have hj := j.isLt; change j.val < 1 at hj; omega
  have hP : (ttFirstGatherParameters m (ttFirstPrefixChoice (min r (min m l)))
      j.val inputBase outputBase).Valid := by
    rw [hj]
    exact prefixGatherParameters_valid m _ inputBase outputBase
      ((Nat.min_le_right r (min m l)).trans (Nat.min_le_left m l))
  refine ⟨hP, ?_⟩
  ext i k
  change U i ⟨_, _⟩ = U i ⟨_, _⟩
  congr 1
  apply Fin.ext
  change (if k.val < min r (min m l) then k.val else _) = k.val
  exact if_pos k.isLt

/-- The actual count/threshold phase chooses exactly explicitFirstFrames for
all legal full decompositions, including empty dimensions and prefix fallback. -/
theorem ttFirstChoice_realizes_explicit {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (r : ℕ) (hr : 1 ≤ r) (inputBase outputBase : ℕ) :
    TTFirstChoiceRealizes U (ttFirstChoice sigma h.2.2.2.1 r (min r (min m l)) hr)
      (explicitFirstFrames h r) inputBase outputBase := by
  classical
  by_cases hrp : r ≤ min m l
  · let a : Fin (min m l) := ⟨r - 1, by omega⟩
    let T := SVD.countedTieStructure sigma h.2.2.2.1 a
    by_cases htau : 0 < sigma a
    · have hc : ttFirstChoice sigma h.2.2.2.1 r (min r (min m l)) hr =
          ⟨T.above, T.tied, T.take, T.tied⟩ := by
        unfold ttFirstChoice
        rw [dif_pos hrp]
        change (if 0 < sigma a then _ else _) = _
        exact if_pos htau
      rw [hc, explicitFirstFrames_eq_positive h r hr hrp htau]
      refine ⟨rfl, T.rank_eq, ?_⟩
      intro j
      refine ⟨tieGatherParameters_valid T j inputBase outputBase, ?_⟩
      exact frameGatherMatrix_tie T j inputBase outputBase U
    · have hc : ttFirstChoice sigma h.2.2.2.1 r (min r (min m l)) hr =
          ttFirstPrefixChoice (min r (min m l)) := by
        unfold ttFirstChoice
        rw [dif_pos hrp]
        change (if 0 < sigma a then _ else _) = _
        exact if_neg htau
      rw [hc, explicitFirstFrames_eq_default_nonpos h r hr hrp (le_of_not_gt htau)]
      exact ttFirstPrefix_realizes h r inputBase outputBase
  · rw [explicitFirstFrames_eq_default_large h r hrp]
    have hc : ttFirstChoice sigma h.2.2.2.1 r (min r (min m l)) hr =
        ttFirstPrefixChoice (min r (min m l)) := by
      exact dif_neg hrp
    rw [hc]
    exact ttFirstPrefix_realizes h r inputBase outputBase

/-- The actual phase endpoint with the original capped first-rank invariant.
Every produced parameter tuple realizes the same explicit family whose
universal strict gate was proved independently of all later child replies. -/
theorem ttFirstSelection_svd_family {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 167) (hs : s.status = .running)
    (hp : s.natural 105 = min (s.natural 81) (s.natural 82))
    (hr : 1 ≤ s.natural 80) (hzero : s.natural 127 = 0)
    (hcap : s.natural 106 = min (s.natural 80) (min (s.natural 81) (s.natural 82)))
    (hd : OutputBlocksDisjoint (s.natural 81) (s.natural 82)
      (s.natural 72) (s.natural 73) (s.natural 74)) :
    ∃ U : Matrix (Fin (s.natural 81)) (Fin (s.natural 81)) ℝ,
    ∃ sigma : Fin (min (s.natural 81) (s.natural 82)) → ℝ,
    ∃ V : Matrix (Fin (s.natural 82)) (Fin (s.natural 82)) ℝ,
    ∃ hvalid : ValidSVD (readMatrix s.memory (s.natural 81) (s.natural 82) (s.natural 92)) U sigma V,
    ∃ n : ℕ,
      n ≤ 9 * min (s.natural 81) (s.natural 82) + 24 ∧
      (trace.state (offset + n)).label = 189 ∧ (trace.state (offset + n)).status = .running ∧
      TTFirstSelected (ttFirstChoice sigma hvalid.2.2.2.1 (s.natural 80)
        (min (s.natural 80) (min (s.natural 81) (s.natural 82))) hr) (trace.state (offset + n)) ∧
      (∀ inputBase outputBase, TTFirstChoiceRealizes U
        (ttFirstChoice sigma hvalid.2.2.2.1 (s.natural 80)
          (min (s.natural 80) (min (s.natural 81) (s.natural 82))) hr)
        (explicitFirstFrames hvalid (s.natural 80)) inputBase outputBase) ∧
      (trace.state (offset + n)).memory =
        writeSVD s.memory (s.natural 72) (s.natural 73) (s.natural 74) U sigma V ∧
      (∀ j : Fin 128, TTFirstProtected j → (trace.state (offset + n)).natural j = s.natural j) ∧
      CostThrough ttProgram trace (offset + n) ≤ CostThrough ttProgram trace offset +
        (s.natural 81 + s.natural 82 + 1)^3 + (9 * min (s.natural 81) (s.natural 82) + 23) := by
  obtain ⟨U, sigma, V, n, hvalid, hn, hlabel, hrun, ⟨hord, hselected⟩, hmemory, hregs, _, _, _, hcost⟩ :=
    ttFirstSelection_svd_run ht offset s he hl hs hp hr hzero hd
  rw [hcap] at hselected
  refine ⟨U, sigma, V, hvalid, n, hn, hlabel, hrun, hselected, ?_, hmemory, hregs, hcost⟩
  intro inputBase outputBase
  exact ttFirstChoice_realizes_explicit hvalid (s.natural 80) hr inputBase outputBase

#assert_trust kernel ttFirstSelection_svd_family
#print axioms ttFirstSelection_svd_family

#assert_trust kernel ttFirstPrefix_realizes
#assert_trust kernel ttFirstChoice_realizes_explicit
#print axioms ttFirstChoice_realizes_explicit
end NLA.Proofs.TR04
