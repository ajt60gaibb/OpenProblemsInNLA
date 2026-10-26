import NLA.Proofs.TR04.TTMemoryLayoutProtection

/-! A concrete stack invariant for the literal forward/reverse TT loops:
original headers/first response, earlier frames/metadata and all candidate
blocks are preserved by every child-stage write. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout

def TTStageProtected (L : Layout) (level address : ℕ) : Prop :=
  address<L.childSigma ∨
    (L.frames≤address ∧ address<L.frame level) ∨
    (L.metadata≤address ∧ address<L.metadata+4*level) ∨ L.store≤address

def TTStageWritable (L : Layout) (level address : ℕ) : Prop :=
  (L.childSigma≤address ∧ address<L.childSigma+L.entries) ∨
    (L.childV≤address ∧ address<L.childV+L.entries^2) ∨
    (L.frame level≤address ∧ address<L.frame level+L.entries^2) ∨
    (L.metadata+4*level≤address ∧ address<L.metadata+4*level+4) ∨
    (L.workA≤address ∧ address<L.store)

theorem ttStageProtected_mono (L : Layout) {level level' address : ℕ}
    (hl : level≤level') (h : TTStageProtected L level address) : TTStageProtected L level' address := by
  have hf : L.frame level≤L.frame level' := by
    unfold Layout.frame
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hl) _
  have hm : L.metadata+4*level≤L.metadata+4*level' := by omega
  rcases h with h|h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h.1,h.2.trans_le hf⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h.1,h.2.trans_le hm⟩))
  · exact Or.inr (Or.inr (Or.inr h))

theorem ttStageProtected_not_writable (L : Layout) (level address : ℕ)
    (hl : level<L.order) (hp : TTStageProtected L level address) :
    ¬TTStageWritable L level address := by
  have hf := L.frame_before_metadata level hl
  have hm : L.metadata+4*level+4≤L.workA := by
    unfold Layout.workA
    omega
  intro hw
  rcases hp with hp|hp|hp|hp <;> rcases hw with hw|hw|hw|hw|hw
  all_goals simp only [Layout.frame,Layout.frames,Layout.childV,Layout.childSigma,
    Layout.metadata,Layout.workA,Layout.store,Layout.workB] at *
  all_goals omega

theorem ttStageProtected_own_frame (L : Layout) (level address : ℕ)
    (ha : L.frame level≤address ∧ address<L.frame level+L.entries^2) :
    TTStageProtected L (level+1) address := by
  apply Or.inr
  apply Or.inl
  unfold Layout.frame at *
  constructor
  · omega
  · nlinarith

theorem ttStageProtected_own_metadata (L : Layout) (level address : ℕ)
    (ha : L.metadata+4*level≤address ∧ address<L.metadata+4*level+4) :
    TTStageProtected L (level+1) address := by
  apply Or.inr
  apply Or.inr
  apply Or.inl
  omega

theorem ttStageProtected_work_outside (L : Layout) (level address base count : ℕ)
    (hl : level<L.order) (hp : TTStageProtected L level address)
    (hb : base=L.workA ∨ base=L.workB) (hc : count≤L.entries) :
    ¬(base≤address ∧ address<base+count) := by
  intro ha
  apply ttStageProtected_not_writable L level address hl hp
  apply Or.inr
  apply Or.inr
  apply Or.inr
  apply Or.inr
  rcases hb with rfl|rfl <;> unfold Layout.store Layout.workB at * <;> omega

theorem ttStageProtected_metadata_outside (L : Layout) (level address field : ℕ)
    (hl : level<L.order) (hp : TTStageProtected L level address) (hf : field<4) :
    address≠L.metadata+4*level+field := by
  intro he
  apply ttStageProtected_not_writable L level address hl hp
  apply Or.inr
  apply Or.inr
  apply Or.inr
  apply Or.inl
  omega

theorem ttStageProtected_child_svd (L : Layout) (level : ℕ) (hl : level<L.order)
    {m l : ℕ} (hm : m≤L.entries) (hc : l≤L.entries) (memory : ℕ → ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) (sigma : Fin (min m l) → ℝ)
    (V : Matrix (Fin l) (Fin l) ℝ) (address : ℕ)
    (hp : TTStageProtected L level address) :
    writeSVD memory (L.frame level) L.childSigma L.childV U sigma V address=memory address := by
  have hu := square_capacity hm
  have hv := square_capacity hc
  have hs : min m l≤L.entries := (Nat.min_le_left _ _).trans hm
  apply writeSVD_outside
  · intro ha
    apply ttStageProtected_not_writable L level address hl hp
    exact Or.inr (Or.inr (Or.inl ⟨ha.1,by omega⟩))
  · intro ha
    apply ttStageProtected_not_writable L level address hl hp
    exact Or.inl ⟨ha.1,by omega⟩
  · intro ha
    apply ttStageProtected_not_writable L level address hl hp
    exact Or.inr (Or.inl ⟨ha.1,by omega⟩)

#assert_trust kernel TTStageProtected
#assert_trust kernel TTStageWritable
#assert_trust kernel ttStageProtected_mono
#assert_trust kernel ttStageProtected_not_writable
#assert_trust kernel ttStageProtected_own_frame
#assert_trust kernel ttStageProtected_own_metadata
#assert_trust kernel ttStageProtected_work_outside
#assert_trust kernel ttStageProtected_metadata_outside
#assert_trust kernel ttStageProtected_child_svd
#print axioms ttStageProtected_child_svd
end NLA.Proofs.TR04
