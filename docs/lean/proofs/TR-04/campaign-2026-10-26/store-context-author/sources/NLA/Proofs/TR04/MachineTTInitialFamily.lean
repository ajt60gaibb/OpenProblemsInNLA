import NLA.Proofs.TR04.MachineTTInitialMemory
import NLA.Proofs.TR04.MachineTTFirstSelectionFamily

/-! Composition from the unchanged original Start through the actual first SVD
and explicit-family selection for every legal full reply. No child reply or
final tensor is supplied at initialization. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation TTMemoryLayout
open TensorFormat.TTStrict

structure TTFirstReply (s : State ttProgram) where
  U : Matrix (Fin (s.natural 81)) (Fin (s.natural 81)) ℝ
  sigma : Fin (min (s.natural 81) (s.natural 82)) → ℝ
  V : Matrix (Fin (s.natural 82)) (Fin (s.natural 82)) ℝ
  valid : ValidSVD (readMatrix s.memory (s.natural 81) (s.natural 82) (s.natural 92)) U sigma V

def TTFirstReply.choice {s : State ttProgram} (R : TTFirstReply s) (hr : 1≤s.natural 80) :
    TTFirstChoice := ttFirstChoice R.sigma R.valid.2.2.2.1 (s.natural 80)
      (min (s.natural 80) (min (s.natural 81) (s.natural 82))) hr

def TTFirstReply.family {s : State ttProgram} (R : TTFirstReply s) : FirstFrames (s.natural 81) (s.natural 80) :=
  explicitFirstFrames R.valid (s.natural 80)

def TTFirstFamilyPhase {s : State ttProgram} (R : TTFirstReply s) (hr : 1≤s.natural 80)
    (t : State ttProgram) : Prop :=
  t.label=189 ∧ t.status=.running ∧ TTFirstSelected (R.choice hr) t ∧
    (∀ inputBase outputBase,TTFirstChoiceRealizes R.U (R.choice hr) R.family inputBase outputBase) ∧
    t.memory=writeSVD s.memory (s.natural 72) (s.natural 73) (s.natural 74) R.U R.sigma R.V ∧
    (∀ j : Fin 128,TTFirstProtected j → t.natural j=s.natural j)

theorem ttFirstSelection_allocation {L : Layout} {s t : State ttProgram}
    (hs : TTAllocationRegisters L s) (hd : t.natural 0=s.natural 0)
    (hn : ∀ j : Fin 128,TTFirstProtected j → t.natural j=s.natural j) : TTAllocationRegisters L t := by
  constructor
  · exact hd.trans hs.order
  all_goals first
    | exact (hn _ (by unfold TTFirstProtected;decide)).trans hs.entries
    | exact (hn _ (by unfold TTFirstProtected;decide)).trans hs.square
    | exact (hn _ (by unfold TTFirstProtected;decide)).trans hs.input
    | exact (hn _ (by unfold TTFirstProtected;decide)).trans hs.firstU
    | exact (hn _ (by unfold TTFirstProtected;decide)).trans hs.firstSigma
    | exact (hn _ (by unfold TTFirstProtected;decide)).trans hs.firstV
    | exact (hn _ (by unfold TTFirstProtected;decide)).trans hs.childSigma
    | exact (hn _ (by unfold TTFirstProtected;decide)).trans hs.childV
    | exact (hn _ (by unfold TTFirstProtected;decide)).trans hs.frames
    | exact (hn _ (by unfold TTFirstProtected;decide)).trans hs.metadata
    | exact (hn _ (by unfold TTFirstProtected;decide)).trans hs.workA
    | exact (hn _ (by unfold TTFirstProtected;decide)).trans hs.workB
    | exact (hn _ (by unfold TTFirstProtected;decide)).trans hs.store
    | exact (hn _ (by unfold TTFirstProtected;decide)).trans hs.four
    | exact (hn _ (by unfold TTFirstProtected;decide)).trans hs.one
    | exact (hn _ (by unfold TTFirstProtected;decide)).trans hs.zero

/-- Every legal original-input trace reaches the exact explicit first-frame
family. The first full reply remains universally arbitrary, and the old input
and every original header remain stored below the first U block. -/
theorem ttInitial_explicit_family (S : Shape) (r : Ranks S) (A : Tensor S)
    (hr : ∀ j,1≤r j) (trace : Trace ttProgram)
    (ht : LegalTrace ttProgram (Start ttProgram S r A) trace) :
    ∃ offset n : ℕ,∃ R : TTFirstReply (trace.state offset),
      offset≤102*(Size S r+1) ∧
      (∃ hi : TTInitialSVDData S r A (trace.state offset),
        TTFirstFamilyPhase R (hi.rank_pos hr) (trace.state (offset+n))) ∧
      n≤9*min ((trace.state offset).natural 81) ((trace.state offset).natural 82)+24 ∧
      TTAllocationRegisters (ofShape S) (trace.state (offset+n)) ∧
      (trace.state (offset+n)).natural 76=0 ∧
      0<(trace.state (offset+n)).natural 75 ∧
      (∀ a,a<(ofShape S).firstU → (trace.state (offset+n)).memory a=InputMemory S r A a) ∧
      readMatrix (trace.state (offset+n)).memory ((trace.state offset).natural 81)
        ((trace.state offset).natural 81) ((trace.state offset).natural 72)=R.U ∧
      (∀ k,(trace.state (offset+n)).memory ((trace.state offset).natural 73+k.val)=R.sigma k) ∧
      readMatrix (trace.state (offset+n)).memory ((trace.state offset).natural 82)
        ((trace.state offset).natural 82) ((trace.state offset).natural 74)=R.V ∧
      offset+n≤1024*(Size S r+1)^3 ∧
      CostThrough ttProgram trace (offset+n)≤1024*(Size S r+1)^3 := by
  obtain ⟨n0,_,hi,hbefore,hbeforeCost⟩ := ttInitial_svd_ready S r A trace ht
  let offset := ttFirstRankEntryTime S r+n0
  let s := trace.state offset
  change offset≤102*(Size S r+1) at hbefore
  change CostThrough ttProgram trace offset≤102*(Size S r+1) at hbeforeCost
  have hpositive := hi.rank_pos hr
  obtain ⟨U,sigma,V,hvalid,n,hn,hl,hs,hselected,hrealizes,hmemory,hnatural,hcost⟩ :=
    ttFirstSelection_svd_family ht offset s rfl hi.label hi.status hi.minimum_eq hpositive
      hi.allocation.zero hi.cap_eq hi.outputsDisjoint
  let R : TTFirstReply s := ⟨U,sigma,V,hvalid⟩
  have hphase : TTFirstFamilyPhase R hpositive (trace.state (offset+n)) :=
    ⟨hl,hs,hselected,hrealizes,hmemory,hnatural⟩
  have horder : (trace.state (offset+n)).natural 0=s.natural 0 :=
    (ttProgram_trace_order S r A trace ht _).trans (ttProgram_trace_order S r A trace ht _).symm
  have ha := ttFirstSelection_allocation hi.allocation horder hnatural
  have hcount : 0<(trace.state (offset+n)).natural 75 := by
    rw [hselected.2.2.2]
    exact ttFirstChoice_count_pos sigma hvalid.2.2.2.1 _ _ hpositive
  have hprefix : ∀ a,a<(ofShape S).firstU →
      (trace.state (offset+n)).memory a=InputMemory S r A a := by
    intro a hat
    rw [hmemory,hi.allocation.firstU,hi.allocation.firstSigma,hi.allocation.firstV]
    exact ((ofShape S).write_firstSVD_prefix s.memory U sigma V a hat).trans (congrFun hi.memory a)
  have hm : s.natural 81≤Size S r := by
    rw [hi.rows]
    exact ttFirstMode_le_size S r
  have hc : s.natural 82≤Size S r := by
    rw [hi.cols]
    exact (ttFirstCols_le_denseSize S).trans (shape_denseSize_le_size S r)
  have hp : min (s.natural 81) (s.natural 82)≤Size S r := (Nat.min_le_left _ _).trans hm
  have hcubic : (s.natural 81+s.natural 82+1)^3≤8*(Size S r+1)^3 := by
    calc
      (s.natural 81+s.natural 82+1)^3≤(2*(Size S r+1))^3 :=
        Nat.pow_le_pow_left (by omega) 3
      _=8*(Size S r+1)^3 := by ring
  have hx : Size S r+1≤(Size S r+1)^3 := Nat.le_self_pow (by decide) _
  refine ⟨offset,n,R,hbefore,⟨hi,hphase⟩,hn,ha,
    (hnatural 76 (by unfold TTFirstProtected;decide)).trans hi.candidateZero,hcount,hprefix,
    ?_,?_,?_,by omega,?_⟩
  · rw [hmemory]
    exact readMatrix_writeSVD_u s.memory _ _ _ U sigma V
  · intro k
    rw [hmemory]
    exact writeSVD_sigma_entry s.memory _ _ _ U sigma V hi.outputsDisjoint k
  · rw [hmemory]
    exact readMatrix_writeSVD_v s.memory _ _ _ U sigma V hi.outputsDisjoint
  · omega

#assert_trust kernel TTFirstReply
#assert_trust kernel TTFirstReply.choice
#assert_trust kernel TTFirstReply.family
#assert_trust kernel TTFirstFamilyPhase
#assert_trust kernel ttFirstSelection_allocation
#assert_trust kernel ttInitial_explicit_family
#print axioms ttInitial_explicit_family
end NLA.Proofs.TR04
