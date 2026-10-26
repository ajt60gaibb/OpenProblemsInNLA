import NLA.Proofs.TR04.MachineTTFirstGather
import NLA.Proofs.TR04.MachineTTStageMetadata

/-! Exact initial-family candidates enter the same actual recursive stage as
full-U child replies. The frame family remains fixed before all child replies. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat TensorFormat.TTStrict TTMemoryLayout

theorem ttFirstCandidate_stage {s0 s t : State ttProgram} {R : TTFirstReply s0}
    {hr : 1≤s0.natural 80} {L : Layout} (h : TTFirstContext R hr L s)
    (ht : TTFirstContext R hr L t) (hf : TTCandidateMetadataFields s t)
    {ns : List ℕ} (A : Tensor (s0.natural 81::ns))
    (hcols : suffixSize ns=s0.natural 82)
    (hread : readMatrix s0.memory (s0.natural 81) (suffixSize ns) (s0.natural 92)=radixDenseFirst A)
    (j : Fin R.family.count) (hq : s.natural 106=R.family.width)
    (hQ : StoresFrame t.memory L.frames R.family.width (R.family.frame j)) :
    TTStageData L 0 (s0.natural 81) R.family.width ns (R.family.frame j) A t := by
  have hstride : t.natural 88=R.family.width := hf.stride.trans hq
  have hinput : t.natural 89=L.input := hf.input.trans h.allocation.input
  constructor
  · exact ht.allocation
  · exact hf.level
  · exact hf.rows.trans h.rows
  · exact hf.width.trans hq
  · exact (hf.cols.trans h.cols).trans hcols.symm
  · simpa only [Layout.frame,Nat.zero_mul,Nat.add_zero] using hf.frame.trans h.allocation.frames
  · exact Or.inl hstride
  · rw [hstride]
    simpa only [Layout.frame,Nat.zero_mul,Nat.add_zero] using hQ
  · rw [hinput]
    apply (storesTensor_readMatrix_iff _ _ A).mpr
    apply Eq.trans _ hread
    ext i k
    have hh := congrFun (congrFun ht.readInput i) (Fin.cast hcols k)
    change t.memory (L.input+i.val*s0.natural 82+k.val)=
      s0.memory (s0.natural 92+i.val*s0.natural 82+k.val) at hh
    rw [←hcols] at hh
    exact hh
  · exact Or.inl ⟨hf.tag,hinput,hf.output.trans h.allocation.workA⟩

#assert_trust kernel ttFirstCandidate_stage
#print axioms ttFirstCandidate_stage
end NLA.Proofs.TR04
