import NLA.Proofs.TR04.MachineTTLoopState
import NLA.Proofs.TR04.MachineTTReverse

/-! Concrete buffer separation and protected-address transport used by the
recursive execution induction. The first stage reads the retained input;
child stages use the two actual allocated work buffers. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat

def TTStageBuffers (L : Layout) (s : State ttProgram) : Prop :=
  (s.natural 108=0 ∧ s.natural 89=L.input ∧ s.natural 90=L.workA) ∨
    (s.natural 108=1 ∧ TTWorkPair L s)

 theorem TTWorkPair.current_ge (L : Layout) (s : State ttProgram) (h : TTWorkPair L s) :
    L.workA≤s.natural 89 := by
  rcases h with ⟨hc,hn⟩|⟨hc,hn⟩
  · rw [hc]
  · rw [hc];unfold Layout.workB;omega

 theorem TTWorkPair.output_choice (L : Layout) (s : State ttProgram) (h : TTWorkPair L s) :
    s.natural 90=L.workA ∨ s.natural 90=L.workB := by
  rcases h with ⟨hc,hn⟩|⟨hc,hn⟩
  · exact Or.inr hn
  · exact Or.inl hn

 theorem TTWorkPair.disjoint (L : Layout) (s : State ttProgram) (h : TTWorkPair L s)
    (a b : ℕ) (ha : a≤L.entries) (hb : b≤L.entries) :
    DisjointBlocks (s.natural 89) a (s.natural 90) b := by
  rcases h with ⟨hc,hn⟩|⟨hc,hn⟩
  · rw [hc,hn]
    exact disjoint_fits L.work_buffers_disjoint (fits_same _ _ _ ha) (fits_same _ _ _ hb)
  · rw [hc,hn]
    exact disjoint_fits (disjoint_symm L.work_buffers_disjoint) (fits_same _ _ _ ha) (fits_same _ _ _ hb)

 theorem TTStageBuffers.output_choice {L : Layout} {s : State ttProgram} (h : TTStageBuffers L s) :
    s.natural 90=L.workA ∨ s.natural 90=L.workB := by
  rcases h with ⟨_,_,hout⟩|⟨_,hp⟩
  · exact Or.inl hout
  · exact hp.output_choice L s

 theorem TTStageBuffers.input_output_disjoint {L : Layout} {s : State ttProgram}
    (h : TTStageBuffers L s) (a b : ℕ) (ha : a≤L.entries) (hb : b≤L.entries) :
    DisjointBlocks (s.natural 89) a (s.natural 90) b := by
  rcases h with ⟨_,hin,hout⟩|⟨_,hp⟩
  · rw [hin,hout]
    exact disjoint_fits (L.before_work_disjoint _ _ L.input_before_workA).1
      (fits_same _ _ _ ha) (fits_same _ _ _ hb)
  · exact hp.disjoint L s a b ha hb

 theorem ttFrame_output_disjoint (L : Layout) (level : ℕ) (hl : level<L.order)
    (m stride output count : ℕ) (hm : m≤L.entries) (hs : stride≤L.entries)
    (hout : output=L.workA ∨ output=L.workB) (hc : count≤L.entries) :
    DisjointBlocks (L.frame level) (m*stride) output count := by
  have hf := rectangle_capacity hm hs
  rcases hout with rfl|rfl
  · exact disjoint_fits (L.frame_work_disjoint level hl).1
      (fits_same _ _ _ hf) (fits_same _ _ _ hc)
  · exact disjoint_fits (L.frame_work_disjoint level hl).2.1
      (fits_same _ _ _ hf) (fits_same _ _ _ hc)

 theorem ttLoopKept_reverse (j : Fin 128) (hj : TTLoopKept j) : TTReverseStable j := by
  simp only [TTLoopKept,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals unfold TTReverseStable TTReverseMetadataStable TTReverseLiftSetupStable TTReverseReturnStable;decide

 theorem TTReverseResult.stagePreserves {old final : State ttProgram}
    {m q : ℕ} {ns : List ℕ} {stride frame input output : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (q::ns)}
    (h : TTReverseResult old final m q ns stride frame input output Q A)
    (L : Layout) (level : ℕ) (hl : level<L.order)
    (hout : output=L.workA ∨ output=L.workB) (hc : m*suffixSize ns≤L.entries) :
    TTStagePreserves L level old final :=
  ⟨fun a ha => h.memoryOutside a (ttStageProtected_work_outside L level a output _ hl ha hout hc),
    fun j hj => h.naturalOutside j (ttLoopKept_reverse j hj)⟩

 theorem TTReverseResult.workPair {old final : State ttProgram}
    {L : Layout} {m q : ℕ} {ns : List ℕ} {stride frame : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (q::ns)}
    (h : TTReverseResult old final m q ns stride frame (old.natural 89) (old.natural 90) Q A)
    (hp : TTWorkPair L old) : TTWorkPair L final := by
  rcases hp with ⟨hc,hn⟩|⟨hc,hn⟩
  · exact Or.inr ⟨h.current.trans hn,h.nextBuffer.trans hc⟩
  · exact Or.inl ⟨h.current.trans hn,h.nextBuffer.trans hc⟩

 theorem ttStagePreserves_header {L : Layout} {level : ℕ} {s t : State ttProgram}
    (h : TTStagePreserves L level s t) (address : ℕ) (ha : address<L.input) :
    t.memory address=s.memory address := by
  apply h.1 address
  apply Or.inl
  unfold Layout.childSigma Layout.firstV Layout.firstSigma Layout.firstU
  omega

#assert_trust kernel TTStageBuffers
#assert_trust kernel TTWorkPair.disjoint
#assert_trust kernel TTStageBuffers.input_output_disjoint
#assert_trust kernel ttFrame_output_disjoint
#assert_trust kernel ttLoopKept_reverse
#assert_trust kernel TTReverseResult.stagePreserves
#assert_trust kernel TTReverseResult.workPair
#assert_trust kernel ttStagePreserves_header
#print axioms TTReverseResult.stagePreserves
end NLA.Proofs.TR04
