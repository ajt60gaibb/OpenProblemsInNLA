import NLA.Proofs.TR04.TTMemoryLayout

/-! Literal output-block disjointness and read protection for the concrete TT
allocation. A dense work buffer has only N entries, so its rectangular-size
premise is stated explicitly whenever it is used. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine

 theorem Layout.first_outputs_disjoint (L : Layout) (m l : ℕ)
    (hm : m ≤ L.entries) (hl : l ≤ L.entries) :
    OutputBlocksDisjoint m l L.firstU L.firstSigma L.firstV := by
  have hu := square_capacity hm
  have hv := square_capacity hl
  have hs : min m l ≤ L.entries := (Nat.min_le_left m l).trans hm
  unfold OutputBlocksDisjoint
  refine ⟨disjoint_of_end_le ?_, disjoint_of_end_le ?_, disjoint_of_end_le ?_⟩
  · unfold Layout.firstSigma; omega
  · unfold Layout.firstV Layout.firstSigma; omega
  · unfold Layout.firstV; omega

 theorem Layout.child_outputs_disjoint (L : Layout) (level m l : ℕ)
    (hm : m ≤ L.entries) (hl : l ≤ L.entries) :
    OutputBlocksDisjoint m l (L.frame level) L.childSigma L.childV := by
  have hv := square_capacity hl
  have hs : min m l ≤ L.entries := (Nat.min_le_left m l).trans hm
  unfold OutputBlocksDisjoint
  refine ⟨disjoint_symm (disjoint_of_end_le ?_),
    disjoint_symm (disjoint_of_end_le ?_), disjoint_of_end_le ?_⟩
  · unfold Layout.frame Layout.frames Layout.childV; omega
  · unfold Layout.frame Layout.frames; omega
  · unfold Layout.childV; omega

 theorem Layout.header_disjoint (L : Layout) (base count : ℕ) (hb : L.input ≤ base) :
    DisjointBlocks 0 L.input base count := by apply disjoint_of_end_le; omega

 theorem Layout.input_disjoint (L : Layout) (base count : ℕ) (hb : L.firstU ≤ base) :
    DisjointBlocks L.input L.entries base count := by
  apply disjoint_of_end_le
  exact hb

 theorem Layout.firstU_before_workA (L : Layout) : L.firstU + L.entries ^ 2 ≤ L.workA := by
  unfold Layout.workA Layout.metadata Layout.frames Layout.childV Layout.childSigma
    Layout.firstV Layout.firstSigma
  omega

 theorem Layout.firstV_before_workA (L : Layout) : L.firstV + L.entries ^ 2 ≤ L.workA := by
  unfold Layout.workA Layout.metadata Layout.frames Layout.childV Layout.childSigma
  omega

 theorem Layout.firstSigma_before_workA (L : Layout) : L.firstSigma + L.entries ≤ L.workA := by
  unfold Layout.workA Layout.metadata Layout.frames Layout.childV Layout.childSigma Layout.firstV
  omega

 theorem Layout.input_before_workA (L : Layout) : L.input + L.entries ≤ L.workA := by
  exact (Nat.le_add_right L.firstU (L.entries ^ 2)).trans L.firstU_before_workA

 theorem Layout.childSigma_before_workA (L : Layout) : L.childSigma + L.entries ≤ L.workA := by
  unfold Layout.workA Layout.metadata Layout.frames Layout.childV
  omega

 theorem Layout.childV_before_workA (L : Layout) : L.childV + L.entries ^ 2 ≤ L.workA := by
  unfold Layout.workA Layout.metadata Layout.frames
  omega

 theorem Layout.frame_before_workA (L : Layout) (level : ℕ) (hl : level < L.order) :
    L.frame level + L.entries ^ 2 ≤ L.workA := by
  have h := L.frame_before_metadata level hl
  unfold Layout.workA
  omega

 theorem Layout.before_work_disjoint (L : Layout) (base count : ℕ)
    (h : base + count ≤ L.workA) :
    DisjointBlocks base count L.workA L.entries ∧
    DisjointBlocks base count L.workB L.entries ∧
    (∀ j, DisjointBlocks base count (L.candidate j) L.entries) := by
  refine ⟨disjoint_of_end_le h, disjoint_of_end_le ?_, ?_⟩
  · unfold Layout.workB; omega
  · intro j; apply disjoint_of_end_le
    unfold Layout.candidate Layout.store Layout.workB; omega

 theorem Layout.work_buffers_disjoint (L : Layout) :
    DisjointBlocks L.workA L.entries L.workB L.entries :=
  disjoint_of_end_le (by unfold Layout.workB; omega)

 theorem Layout.workA_candidate_disjoint (L : Layout) (j : ℕ) :
    DisjointBlocks L.workA L.entries (L.candidate j) L.entries := by
  apply disjoint_of_end_le
  unfold Layout.candidate Layout.store Layout.workB
  omega

 theorem Layout.workB_candidate_disjoint (L : Layout) (j : ℕ) :
    DisjointBlocks L.workB L.entries (L.candidate j) L.entries := by
  apply disjoint_of_end_le
  unfold Layout.candidate Layout.store
  omega

 theorem Layout.frame_metadata_disjoint (L : Layout) (level : ℕ) (hl : level < L.order) :
    DisjointBlocks (L.frame level) (L.entries ^ 2) L.metadata (4 * L.order) :=
  disjoint_of_end_le (L.frame_before_metadata level hl)

 theorem Layout.frame_work_disjoint (L : Layout) (level : ℕ) (hl : level < L.order) :
    DisjointBlocks (L.frame level) (L.entries ^ 2) L.workA L.entries ∧
    DisjointBlocks (L.frame level) (L.entries ^ 2) L.workB L.entries ∧
    (∀ j, DisjointBlocks (L.frame level) (L.entries ^ 2) (L.candidate j) L.entries) :=
  L.before_work_disjoint _ _ (L.frame_before_workA level hl)

 theorem Layout.frame_rectangle_fits (L : Layout) (level m q : ℕ)
    (hm : m ≤ L.entries) (hq : q ≤ L.entries) :
    Fits (L.frame level) (m * q) (L.frame level) (L.entries ^ 2) :=
  fits_same _ _ _ (rectangle_capacity hm hq)

 theorem Layout.workA_rectangle_fits (L : Layout) (m l : ℕ) (h : m * l ≤ L.entries) :
    Fits L.workA (m * l) L.workA L.entries := fits_same _ _ _ h

 theorem Layout.workB_rectangle_fits (L : Layout) (m l : ℕ) (h : m * l ≤ L.entries) :
    Fits L.workB (m * l) L.workB L.entries := fits_same _ _ _ h

 theorem Layout.frame_workA_rectangle_disjoint (L : Layout) (level m q a b : ℕ)
    (hlevel : level < L.order) (hm : m ≤ L.entries) (hq : q ≤ L.entries)
    (hab : a * b ≤ L.entries) :
    DisjointBlocks (L.frame level) (m * q) L.workA (a * b) :=
  disjoint_fits (L.frame_work_disjoint level hlevel).1
    (L.frame_rectangle_fits level m q hm hq) (L.workA_rectangle_fits a b hab)

 theorem Layout.work_rectangle_disjoint (L : Layout) (m l a b : ℕ)
    (hml : m * l ≤ L.entries) (hab : a * b ≤ L.entries) :
    DisjointBlocks L.workA (m * l) L.workB (a * b) :=
  disjoint_fits L.work_buffers_disjoint
    (L.workA_rectangle_fits m l hml) (L.workB_rectangle_fits a b hab)

 theorem writeSVD_preserves_disjoint_block {m l : ℕ} (memory : ℕ → ℝ)
    (ub sb vb savedBase count address : ℕ) (U : Matrix (Fin m) (Fin m) ℝ)
    (sigma : Fin (min m l) → ℝ) (V : Matrix (Fin l) (Fin l) ℝ)
    (hu : DisjointBlocks ub (m * m) savedBase count)
    (hs : DisjointBlocks sb (min m l) savedBase count)
    (hv : DisjointBlocks vb (l * l) savedBase count)
    (ha : savedBase ≤ address ∧ address < savedBase + count) :
    writeSVD memory ub sb vb U sigma V address = memory address :=
  NLA.Proofs.TR04.writeSVD_outside memory ub sb vb U sigma V address
    (NLA.Proofs.TR04.disjointBlocks_not_mem_left hu ha)
    (NLA.Proofs.TR04.disjointBlocks_not_mem_left hs ha)
    (NLA.Proofs.TR04.disjointBlocks_not_mem_left hv ha)

 theorem Layout.write_firstSVD_prefix (L : Layout) {m l : ℕ} (memory : ℕ → ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) (sigma : Fin (min m l) → ℝ)
    (V : Matrix (Fin l) (Fin l) ℝ) (address : ℕ) (ha : address < L.firstU) :
    writeSVD memory L.firstU L.firstSigma L.firstV U sigma V address = memory address := by
  apply NLA.Proofs.TR04.writeSVD_outside
  · omega
  · unfold Layout.firstSigma; omega
  · unfold Layout.firstV Layout.firstSigma; omega

 theorem Layout.write_childSVD_work (L : Layout) (level : ℕ) (hlevel : level < L.order)
    {m l : ℕ} (memory : ℕ → ℝ) (U : Matrix (Fin m) (Fin m) ℝ)
    (sigma : Fin (min m l) → ℝ) (V : Matrix (Fin l) (Fin l) ℝ)
    (hm : m ≤ L.entries) (hl : l ≤ L.entries)
    (address : ℕ) (ha : L.workA ≤ address) :
    writeSVD memory (L.frame level) L.childSigma L.childV U sigma V address = memory address := by
  have hu := square_capacity hm
  have hv := square_capacity hl
  have hs : min m l ≤ L.entries := (Nat.min_le_left m l).trans hm
  have hfu := L.frame_before_workA level hlevel
  have hfs := L.childSigma_before_workA
  have hfv := L.childV_before_workA
  apply NLA.Proofs.TR04.writeSVD_outside <;> omega

theorem Layout.firstU_frame_disjoint (L : Layout) (level m q : ℕ)
    (hm : m ≤ L.entries) :
    DisjointBlocks L.firstU (m * m) (L.frame level) (m * q) := by
  have hu := square_capacity hm
  apply disjoint_of_end_le
  unfold Layout.frame Layout.frames Layout.childV Layout.childSigma Layout.firstV Layout.firstSigma
  omega

theorem Layout.write_firstSVD_later (L : Layout) {m l : ℕ} (memory : ℕ → ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) (sigma : Fin (min m l) → ℝ)
    (V : Matrix (Fin l) (Fin l) ℝ) (hm : m ≤ L.entries) (hl : l ≤ L.entries)
    (address : ℕ) (ha : L.childSigma ≤ address) :
    writeSVD memory L.firstU L.firstSigma L.firstV U sigma V address = memory address := by
  have hu := square_capacity hm
  have hv := square_capacity hl
  have hs : min m l ≤ L.entries := (Nat.min_le_left m l).trans hm
  apply NLA.Proofs.TR04.writeSVD_outside
  · unfold Layout.childSigma Layout.firstV Layout.firstSigma at ha; omega
  · unfold Layout.childSigma Layout.firstV at ha; omega
  · unfold Layout.childSigma at ha; omega

theorem Layout.write_childSVD_other_frame (L : Layout) (level other : ℕ)
    (hne : level ≠ other) {m l : ℕ} (memory : ℕ → ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) (sigma : Fin (min m l) → ℝ)
    (V : Matrix (Fin l) (Fin l) ℝ) (hm : m ≤ L.entries) (hl : l ≤ L.entries)
    (address : ℕ)
    (ha : L.frame other ≤ address ∧ address < L.frame other + L.entries ^ 2) :
    writeSVD memory (L.frame level) L.childSigma L.childV U sigma V address = memory address := by
  apply writeSVD_preserves_disjoint_block memory _ _ _ (L.frame other) (L.entries ^ 2)
    address U sigma V _ _ _ ha
  · exact disjoint_fits (L.frames_disjoint level other hne)
      (fits_same _ _ _ (square_capacity hm)) (fits_same _ _ _ le_rfl)
  · apply disjoint_of_end_le
    have hs : min m l ≤ L.entries := (Nat.min_le_left m l).trans hm
    unfold Layout.frame Layout.frames Layout.childV; omega
  · apply disjoint_of_end_le
    have hv := square_capacity hl
    unfold Layout.frame Layout.frames; omega

#assert_trust kernel Layout.first_outputs_disjoint
#assert_trust kernel Layout.child_outputs_disjoint
#assert_trust kernel Layout.frame_workA_rectangle_disjoint
#assert_trust kernel Layout.work_rectangle_disjoint
#assert_trust kernel Layout.write_childSVD_work
#print axioms Layout.first_outputs_disjoint
#print axioms Layout.child_outputs_disjoint
#print axioms Layout.write_childSVD_work
end NLA.Proofs.TR04.TTMemoryLayout
