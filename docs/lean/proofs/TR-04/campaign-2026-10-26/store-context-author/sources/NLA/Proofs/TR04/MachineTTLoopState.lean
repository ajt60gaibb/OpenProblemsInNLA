import NLA.Proofs.TR04.MachineTTStageProtection
import NLA.Proofs.TR04.MachineTTStartup
import NLA.Proofs.TR04.MachineTTMetadata
import NLA.Proofs.TR04.MachineTTForward
import NLA.Proofs.TR04.MachineTTChildInitializationHelpers

/-! Common actual state invariant for recursive TT execution. This protects
only literal global registers and address regions; approximation and capacity
claims are separately derived from original inputs and actual SVD responses. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat

def TTLoopKept (j : Fin 128) : Prop :=
  j ∈ ([0,64,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,92,
    103,104,105,106,125,126,127] : List (Fin 128))

def TTStagePreserves (L : Layout) (level : ℕ) (s t : State ttProgram) : Prop :=
  (∀ address,TTStageProtected L level address → t.memory address=s.memory address) ∧
    ∀ j : Fin 128,TTLoopKept j → t.natural j=s.natural j

def TTWorkPair (L : Layout) (s : State ttProgram) : Prop :=
  (s.natural 89=L.workA ∧ s.natural 90=L.workB) ∨
    (s.natural 89=L.workB ∧ s.natural 90=L.workA)

theorem ttStagePreserves_refl (L : Layout) (level : ℕ) (s : State ttProgram) :
    TTStagePreserves L level s s := ⟨fun _ _ => rfl,fun _ _ => rfl⟩

theorem ttStagePreserves_trans {L : Layout} {level : ℕ} {s t u : State ttProgram}
    (h : TTStagePreserves L level s t) (k : TTStagePreserves L level t u) :
    TTStagePreserves L level s u :=
  ⟨fun a ha => (k.1 a ha).trans (h.1 a ha),fun j hj => (k.2 j hj).trans (h.2 j hj)⟩

theorem ttStagePreserves_lower {L : Layout} {level level' : ℕ} {s t : State ttProgram}
    (h : TTStagePreserves L level' s t) (hl : level≤level') : TTStagePreserves L level s t :=
  ⟨fun a ha => h.1 a (ttStageProtected_mono L hl ha),h.2⟩

theorem ttStagePreserves_allocation {L : Layout} {level : ℕ} {s t : State ttProgram}
    (h : TTStagePreserves L level s t) (hs : TTAllocationRegisters L s) : TTAllocationRegisters L t := by
  constructor
  all_goals first
    | exact (h.2 _ (by unfold TTLoopKept;decide)).trans hs.order
    | exact (h.2 _ (by unfold TTLoopKept;decide)).trans hs.entries
    | exact (h.2 _ (by unfold TTLoopKept;decide)).trans hs.square
    | exact (h.2 _ (by unfold TTLoopKept;decide)).trans hs.input
    | exact (h.2 _ (by unfold TTLoopKept;decide)).trans hs.firstU
    | exact (h.2 _ (by unfold TTLoopKept;decide)).trans hs.firstSigma
    | exact (h.2 _ (by unfold TTLoopKept;decide)).trans hs.firstV
    | exact (h.2 _ (by unfold TTLoopKept;decide)).trans hs.childSigma
    | exact (h.2 _ (by unfold TTLoopKept;decide)).trans hs.childV
    | exact (h.2 _ (by unfold TTLoopKept;decide)).trans hs.frames
    | exact (h.2 _ (by unfold TTLoopKept;decide)).trans hs.metadata
    | exact (h.2 _ (by unfold TTLoopKept;decide)).trans hs.workA
    | exact (h.2 _ (by unfold TTLoopKept;decide)).trans hs.workB
    | exact (h.2 _ (by unfold TTLoopKept;decide)).trans hs.store
    | exact (h.2 _ (by unfold TTLoopKept;decide)).trans hs.four
    | exact (h.2 _ (by unfold TTLoopKept;decide)).trans hs.one
    | exact (h.2 _ (by unfold TTLoopKept;decide)).trans hs.zero

theorem ttLoopKept_not_metadataScratch (j : Fin 128) (hj : TTLoopKept j) : j≠93 := by
  simp only [TTLoopKept,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

theorem ttLoopKept_child (j : Fin 128) (hj : TTLoopKept j) : TTChildKept j := by
  simp only [TTLoopKept,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals unfold TTChildKept;decide

theorem ttLoopKept_forward (j : Fin 128) (hj : TTLoopKept j) : TTForwardStable j := by
  simp only [TTLoopKept,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals unfold TTForwardStable TTForwardReturnStable;decide

theorem ttChildPreserves_stage {L : Layout} {level : ℕ} {s t : State ttProgram}
    (h : TTChildPreserves s t) : TTStagePreserves L level s t :=
  ⟨fun a _ => congrFun h.1 a,fun j hj => h.2 j (ttLoopKept_child j hj)⟩

theorem TTForwardResult.stagePreserves {old final : State ttProgram}
    {m q : ℕ} {ns : List ℕ} {stride frame input output next : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (m::ns)}
    (h : TTForwardResult old final m q ns stride frame input output next Q A)
    (L : Layout) (level : ℕ) (hl : level<L.order)
    (hb : output=L.workA ∨ output=L.workB) (hc : q*suffixSize ns≤L.entries) :
    TTStagePreserves L level old final :=
  ⟨fun a ha => h.memoryOutside a (ttStageProtected_work_outside L level a output _ hl ha hb hc),
    fun j hj => h.naturalOutside j (ttLoopKept_forward j hj)⟩

theorem ttMetadata_stagePreserves_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (L : Layout) (level : ℕ)
    (hlevel : level<L.order)
    (hl : (trace.state offset).label=241) (hs : (trace.state offset).status=.running)
    (hmeta : (trace.state offset).natural 68=L.metadata)
    (hfour : (trace.state offset).natural 125=4) (hlev : (trace.state offset).natural 84=level) :
    TTStagePreserves L level (trace.state offset) (trace.state (offset+14)) := by
  obtain ⟨_,_,_,_,hm,hn,_,_⟩ := ttMetadata_fields_at ht offset L level hl hs hmeta hfour hlev
  constructor
  · intro a ha
    apply hm a
    intro hw
    apply ttStageProtected_not_writable L level a hlevel ha
    exact Or.inr (Or.inr (Or.inr (Or.inl hw)))
  · intro j hj
    exact hn j (ttLoopKept_not_metadataScratch j hj)

theorem ttStagePreserves_prior_frame {L : Layout} {level : ℕ} {s t : State ttProgram}
    (h : TTStagePreserves L (level+1) s t) {m q stride : ℕ}
    (Q : Matrix (Fin m) (Fin q) ℝ) (hq : q≤stride)
    (hm : m≤L.entries) (hstride : stride≤L.entries)
    (hQ : StoresFrame s.memory (L.frame level) stride Q) :
    StoresFrame t.memory (L.frame level) stride Q := by
  apply hQ.memory_eq hq
  intro a ha
  apply h.1 a
  apply ttStageProtected_own_frame L level a
  have hc := rectangle_capacity hm hstride
  omega

theorem ttStagePreserves_prior_metadata {L : Layout} {level : ℕ} {s t : State ttProgram}
    (h : TTStagePreserves L (level+1) s t) (field : Fin 4) :
    t.memory (L.metadataCell level field.val)=s.memory (L.metadataCell level field.val) := by
  apply h.1
  apply ttStageProtected_own_metadata L level
  unfold Layout.metadataCell
  have := field.isLt
  omega

theorem ttLoopKept_not_childSvdScratch (j : Fin 128) (hj : TTLoopKept j) : j≠88 ∧ j≠108 := by
  simp only [TTLoopKept,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

theorem ttStagePreserves_of_childSvd {L : Layout} {level : ℕ} {s t : State ttProgram}
    (hm : ∀ a,TTStageProtected L level a → t.memory a=s.memory a)
    (hn : ∀ j : Fin 128,j≠88 → j≠108 → t.natural j=s.natural j) :
    TTStagePreserves L level s t :=
  ⟨hm,fun j hj => hn j (ttLoopKept_not_childSvdScratch j hj).1
    (ttLoopKept_not_childSvdScratch j hj).2⟩

#assert_trust kernel ttLoopKept_not_childSvdScratch
#assert_trust kernel ttStagePreserves_of_childSvd
#assert_trust kernel TTLoopKept
#assert_trust kernel TTStagePreserves
#assert_trust kernel TTWorkPair
#assert_trust kernel ttStagePreserves_refl
#assert_trust kernel ttStagePreserves_trans
#assert_trust kernel ttStagePreserves_lower
#assert_trust kernel ttStagePreserves_allocation
#assert_trust kernel ttLoopKept_not_metadataScratch
#assert_trust kernel ttLoopKept_child
#assert_trust kernel ttLoopKept_forward
#assert_trust kernel ttChildPreserves_stage
#assert_trust kernel TTForwardResult.stagePreserves
#assert_trust kernel ttMetadata_stagePreserves_at
#assert_trust kernel ttStagePreserves_prior_frame
#assert_trust kernel ttStagePreserves_prior_metadata
#print axioms ttStagePreserves_prior_frame
#print axioms ttMetadata_stagePreserves_at
end NLA.Proofs.TR04
