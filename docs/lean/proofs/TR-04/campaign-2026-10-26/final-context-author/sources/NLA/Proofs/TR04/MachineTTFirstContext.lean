import NLA.Proofs.TR04.MachineTTInitialFamily
import NLA.Proofs.TR04.MachineTTLoopState

/-! The fixed first reply and its explicit frame family survive each actual
candidate. Bounds follow from the original dense shape and finite tie block. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation TTMemoryLayout

/-- A tie block has at most p columns; the fallback uses one candidate. -/
theorem ttFirstChoice_count_le {p : ℕ} (sigma : Fin p → ℝ) (hord : Antitone sigma)
    (r cap : ℕ) (hr : 1≤r) (N : ℕ) (hp : p≤N) (hN : 0<N) :
    (ttFirstChoice sigma hord r cap hr).count≤N := by
  unfold ttFirstChoice
  split
  · dsimp only
    split
    · have h := (SVD.countedTieStructure sigma hord (⟨r-1,by omega⟩ : Fin p)).fits
      change (SVD.countedTieStructure sigma hord (⟨r-1,by omega⟩ : Fin p)).tied≤N
      omega
    · exact hN
  · exact hN

structure TTFirstContext {s0 : State ttProgram} (R : TTFirstReply s0)
    (hr : 1≤s0.natural 80) (L : Layout) (s : State ttProgram) : Prop where
  allocation : TTAllocationRegisters L s
  rows : s.natural 81=s0.natural 81
  cols : s.natural 82=s0.natural 82
  rank : s.natural 80=s0.natural 80
  cap : s.natural 106=min (s0.natural 80) (min (s0.natural 81) (s0.natural 82))
  selected : TTFirstSelected (R.choice hr) s
  rows_le : s0.natural 81≤L.entries
  cols_le : s0.natural 82≤L.entries
  input_count : s0.natural 81*s0.natural 82=L.entries
  entries_pos : 0<L.entries
  order_pos : 0<L.order
  savedPrefix : ∀ a,a<L.firstU → s.memory a=s0.memory a
  readInput : readMatrix s.memory (s0.natural 81) (s0.natural 82) L.input=
    readMatrix s0.memory (s0.natural 81) (s0.natural 82) (s0.natural 92)
  readU : readMatrix s.memory (s0.natural 81) (s0.natural 81) L.firstU=R.U
  readSigma : ∀ k,s.memory (L.firstSigma+k.val)=R.sigma k
  readV : readMatrix s.memory (s0.natural 82) (s0.natural 82) L.firstV=R.V

theorem TTFirstContext.count_le {s0 s : State ttProgram} {R : TTFirstReply s0}
    {hr : 1≤s0.natural 80} {L : Layout} (h : TTFirstContext R hr L s) :
    s.natural 75≤L.entries := by
  rw [h.selected.2.2.2]
  exact ttFirstChoice_count_le R.sigma R.valid.2.2.2.1 _ _ hr _
    ((Nat.min_le_left _ _).trans h.rows_le) h.entries_pos

theorem TTFirstContext.count_eq {s0 s : State ttProgram} {R : TTFirstReply s0}
    {hr : 1≤s0.natural 80} {L : Layout} (h : TTFirstContext R hr L s) :
    s.natural 75=R.family.count := by
  obtain ⟨hc,_,_⟩ := ttFirstChoice_realizes_explicit R.valid (s0.natural 80) hr 0 0
  exact h.selected.2.2.2.trans hc

/-- Transfer only reads below childSigma and the actual global registers.
The candidate index is intentionally allowed to increase after its copy. -/
theorem TTFirstContext.transfer {s0 s t : State ttProgram} {R : TTFirstReply s0}
    {hr : 1≤s0.natural 80} {L : Layout} (h : TTFirstContext R hr L s)
    (hm : ∀ a,a<L.childSigma → t.memory a=s.memory a)
    (hn : ∀ j : Fin 128,TTLoopKept j → j≠76 → t.natural j=s.natural j) :
    TTFirstContext R hr L t := by
  have hkept (j : Fin 128) (hj : TTLoopKept j) (hneq : j≠76) := hn j hj hneq
  have ha : TTAllocationRegisters L t := by
    constructor
    all_goals first
      | exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.allocation.order
      | exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.allocation.entries
      | exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.allocation.square
      | exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.allocation.input
      | exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.allocation.firstU
      | exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.allocation.firstSigma
      | exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.allocation.firstV
      | exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.allocation.childSigma
      | exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.allocation.childV
      | exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.allocation.frames
      | exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.allocation.metadata
      | exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.allocation.workA
      | exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.allocation.workB
      | exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.allocation.store
      | exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.allocation.four
      | exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.allocation.one
      | exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.allocation.zero
  have hs : TTFirstSelected (R.choice hr) t := by
    refine ⟨?_,?_,?_,?_⟩
    · exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.selected.1
    · exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.selected.2.1
    · exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.selected.2.2.1
    · exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.selected.2.2.2
  have hread (base rows cols : ℕ) (hend : base+rows*cols≤L.childSigma) :
      readMatrix t.memory rows cols base=readMatrix s.memory rows cols base := by
    ext i k
    exact hm _ (by have hh := matrix_offset_lt i k;omega)
  have hu := square_capacity h.rows_le
  have hv := square_capacity h.cols_le
  refine ⟨ha,?_,?_,?_,?_,hs,h.rows_le,h.cols_le,h.input_count,h.entries_pos,h.order_pos,?_,?_,?_,?_,?_⟩
  · exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.rows
  · exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.cols
  · exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.rank
  · exact (hkept _ (by unfold TTLoopKept;decide) (by decide)).trans h.cap
  · intro a ha
    exact (hm a (by unfold Layout.childSigma Layout.firstV Layout.firstSigma;omega)).trans (h.savedPrefix a ha)
  · apply Eq.trans (hread _ _ _ ?_) h.readInput
    rw [h.input_count]
    unfold Layout.childSigma Layout.firstV Layout.firstSigma Layout.firstU
    omega
  · apply Eq.trans (hread _ _ _ ?_) h.readU
    unfold Layout.childSigma Layout.firstV Layout.firstSigma
    omega
  · intro k
    exact (hm _ (by
      have hh := k.isLt
      have hp := Nat.min_le_left (s0.natural 81) (s0.natural 82)
      have hb := h.rows_le
      unfold Layout.childSigma Layout.firstV
      omega)).trans (h.readSigma k)
  · apply Eq.trans (hread _ _ _ ?_) h.readV
    unfold Layout.childSigma
    omega

theorem TTFirstContext.of_stage {s0 s t : State ttProgram} {R : TTFirstReply s0}
    {hr : 1≤s0.natural 80} {L : Layout} (h : TTFirstContext R hr L s)
    {level : ℕ} (hp : TTStagePreserves L level s t) : TTFirstContext R hr L t :=
  h.transfer (fun a ha => hp.1 a (Or.inl ha)) (fun j hj _ => hp.2 j hj)

/-- The actual original first-family endpoint initializes the fixed context. -/
theorem TTFirstFamilyPhase.context {S : Shape} {r : Ranks S} {A : Tensor S}
    {s0 t : State ttProgram} (hi : TTInitialSVDData S r A s0)
    {R : TTFirstReply s0} {hr : 1≤s0.natural 80} (h : TTFirstFamilyPhase R hr t)
    (ha : TTAllocationRegisters (ofShape S) t) : TTFirstContext R hr (ofShape S) t := by
  obtain ⟨_,_,hselected,_,hm,hn⟩ := h
  let L := ofShape S
  have hmemory : t.memory=writeSVD s0.memory L.firstU L.firstSigma L.firstV R.U R.sigma R.V := by
    rw [hm,hi.allocation.firstU,hi.allocation.firstSigma,hi.allocation.firstV]
  have hrows : s0.natural 81≤L.entries := by
    rw [hi.rows]
    exact ttFirstMode_le_denseSize S
  have hcols : s0.natural 82≤L.entries := by
    rw [hi.cols]
    exact ttFirstCols_le_denseSize S
  have hcount : s0.natural 81*s0.natural 82=L.entries := by
    rw [hi.rows,hi.cols]
    exact ttFirstCols_prod S
  have hpref : ∀ a,a<L.firstU → t.memory a=s0.memory a := by
    intro a ha
    rw [hmemory]
    exact L.write_firstSVD_prefix s0.memory R.U R.sigma R.V a ha
  have hd : OutputBlocksDisjoint (s0.natural 81) (s0.natural 82) L.firstU L.firstSigma L.firstV := by
    rw [←hi.allocation.firstU,←hi.allocation.firstSigma,←hi.allocation.firstV]
    exact hi.outputsDisjoint
  refine ⟨ha,hn 81 (by unfold TTFirstProtected;decide),hn 82 (by unfold TTFirstProtected;decide),
    hn 80 (by unfold TTFirstProtected;decide),
    (hn 106 (by unfold TTFirstProtected;decide)).trans hi.cap_eq,hselected,
    hrows,hcols,hcount,shape_denseSize_pos S,(by have := S.order_ge;exact lt_of_lt_of_le (by decide : 0<3) this),hpref,?_,?_,?_,?_⟩
  · rw [hi.allocation.input]
    ext i k
    apply hpref
    have hh := matrix_offset_lt i k
    change L.input+i.val*s0.natural 82+k.val<L.input+L.entries
    omega
  · rw [hmemory]
    exact readMatrix_writeSVD_u s0.memory _ _ _ R.U R.sigma R.V
  · intro k
    rw [hmemory]
    exact writeSVD_sigma_entry s0.memory _ _ _ R.U R.sigma R.V hd k
  · rw [hmemory]
    exact readMatrix_writeSVD_v s0.memory _ _ _ R.U R.sigma R.V hd

#assert_trust kernel ttFirstChoice_count_le
#assert_trust kernel TTFirstContext
#assert_trust kernel TTFirstContext.count_le
#assert_trust kernel TTFirstContext.count_eq
#assert_trust kernel TTFirstContext.transfer
#assert_trust kernel TTFirstContext.of_stage
#assert_trust kernel TTFirstFamilyPhase.context
#print axioms TTFirstContext.transfer
#print axioms TTFirstFamilyPhase.context
end NLA.Proofs.TR04
