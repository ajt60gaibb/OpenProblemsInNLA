import NLA.Proofs.TR04.MachineTTFirstContext
import NLA.Proofs.TR04.MachineTTCandidateGatherProtection

/-! Materialize each frame of the one fixed initial family, preserving its
actual saved first reply, original input, and all already stored candidates. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat TensorFormat.TTStrict TTMemoryLayout

theorem ttLoopKept_candidate (j : Fin 128) (hj : TTLoopKept j) : TTCandidateProtectedNat j := by
  simp only [TTLoopKept,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals unfold TTCandidateProtectedNat TTCandidateOutsideBank TTCandidateOutsideResult;decide

theorem TTFirstContext.gather {start s0 : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset=s) (hl : s.label=189) (hs : s.status=.running)
    {R : TTFirstReply s0} {hr : 1≤s0.natural 80} {L : Layout}
    (h : TTFirstContext R hr L s) (hj : s.natural 76<s.natural 75) :
    let time := s0.natural 81*(11*s.natural 106+7)+24
    let t := trace.state (offset+time)
    ∃ j : Fin R.family.count,j.val=s.natural 76 ∧ s.natural 106=R.family.width ∧
      time≤24*(L.entries+1)^2 ∧ t.label=241 ∧ t.status=.running ∧
      StoresFrame t.memory L.frames R.family.width (R.family.frame j) ∧
      TTFirstContext R hr L t ∧ TTStagePreserves L 0 s t ∧
      TTCandidateMetadataFields s t ∧
      CostThrough ttProgram trace (offset+time)≤CostThrough ttProgram trace offset+24*(L.entries+1)^2 := by
  have H := @ttCandidateGather_protected start trace ht offset s he hl hs
  rw [h.rows,h.cols,h.rank] at H
  have hU : StoresFrame s.memory (s.natural 72) (s0.natural 81) R.U := by
    rw [h.allocation.firstU]
    exact (storesFrame_dense_iff _ _ R.U).mpr h.readU
  have hSigma : ∀ k,s.memory (s.natural 73+k.val)=R.sigma k := by
    rw [h.allocation.firstSigma]
    exact h.readSigma
  have hV : readMatrix s.memory (s0.natural 82) (s0.natural 82) (s.natural 74)=R.V := by
    rw [h.allocation.firstV]
    exact h.readV
  have hwidth : s.natural 106≤L.entries := by
    rw [h.cap]
    exact ((Nat.min_le_right _ _).trans (Nat.min_le_left _ _)).trans h.rows_le
  obtain ⟨j,hjval,hq,hbound,hlabel,hrun,hQ,_,_,_,_,hout,hfields,_,_,_,_,hn,_,hc⟩ :=
    H R.valid hr h.cap h.selected hj hU hSigma hV L h.rows_le hwidth h.cols_le
      h.allocation.firstU h.allocation.firstSigma h.allocation.firstV h.allocation.frames h.allocation.input
  have hp : TTStagePreserves L 0 s
      (trace.state (offset+(s0.natural 81*(11*s.natural 106+7)+24))) := by
    refine ⟨?_,fun k hk => hn k (ttLoopKept_candidate k hk)⟩
    intro a ha
    apply hout
    rw [h.allocation.frames]
    intro hwrite
    have hrect := rectangle_capacity h.rows_le hwidth
    exact ttStageProtected_not_writable L 0 a h.order_pos ha (Or.inr (Or.inr (Or.inl (by
        simpa only [Layout.frame,Nat.zero_mul,Nat.add_zero] using
          And.intro hwrite.1 (lt_of_lt_of_le hwrite.2 (Nat.add_le_add_left hrect _))))))
  refine ⟨j,hjval,hq,hbound,hlabel,hrun,?_,h.of_stage hp,hp,hfields,hc⟩
  rw [h.allocation.frames] at hQ
  exact hQ

#assert_trust kernel ttLoopKept_candidate
#assert_trust kernel TTFirstContext.gather
#print axioms TTFirstContext.gather
end NLA.Proofs.TR04
