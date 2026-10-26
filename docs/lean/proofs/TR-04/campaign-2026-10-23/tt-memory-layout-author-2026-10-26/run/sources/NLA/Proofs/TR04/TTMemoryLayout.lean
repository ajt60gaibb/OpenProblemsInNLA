import NLA.Proofs.TR04.MachineSVDMemory
import NLA.Proofs.TR04.ShapeInitializationBounds

/-! Concrete finite TT allocation. All lengths are natural numbers; empty
blocks and zero dimensions obey the literal SVD machine's block convention. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
open NLA.Computation.TensorTrainApproximation

structure Layout where
  order : ℕ
  entries : ℕ

def ofShape (S : Shape) : Layout := ⟨S.order, DenseSize S⟩

def Layout.input (L : Layout) : ℕ := 2 * L.order - 1
def Layout.firstU (L : Layout) : ℕ := L.input + L.entries
def Layout.firstSigma (L : Layout) : ℕ := L.firstU + L.entries ^ 2
def Layout.firstV (L : Layout) : ℕ := L.firstSigma + L.entries
def Layout.childSigma (L : Layout) : ℕ := L.firstV + L.entries ^ 2
def Layout.childV (L : Layout) : ℕ := L.childSigma + L.entries
def Layout.frames (L : Layout) : ℕ := L.childV + L.entries ^ 2
def Layout.frame (L : Layout) (level : ℕ) : ℕ := L.frames + level * L.entries ^ 2
def Layout.metadata (L : Layout) : ℕ := L.frames + L.order * L.entries ^ 2
def Layout.metadataCell (L : Layout) (level field : ℕ) : ℕ :=
  L.metadata + 4 * level + field
def Layout.workA (L : Layout) : ℕ := L.metadata + 4 * L.order
def Layout.workB (L : Layout) : ℕ := L.workA + L.entries
def Layout.store (L : Layout) : ℕ := L.workB + L.entries
def Layout.candidate (L : Layout) (j : ℕ) : ℕ := L.store + j * L.entries
def Layout.endAddress (L : Layout) (count : ℕ) : ℕ := L.store + count * L.entries

/-- Literal half-open containment of a possibly empty subblock. -/
def Fits (base count outer capacity : ℕ) : Prop :=
  outer ≤ base ∧ base + count ≤ outer + capacity

theorem fits_same (base count capacity : ℕ) (h : count ≤ capacity) :
    Fits base count base capacity := by unfold Fits; omega

theorem fits_trans {a n b m c k : ℕ} (ha : Fits a n b m) (hb : Fits b m c k) :
    Fits a n c k := by unfold Fits at *; omega

theorem disjoint_symm {a n b m : ℕ} (h : DisjointBlocks a n b m) :
    DisjointBlocks b m a n := by unfold DisjointBlocks at *; omega

theorem disjoint_of_end_le {a n b m : ℕ} (h : a + n ≤ b) :
    DisjointBlocks a n b m := Or.inr (Or.inr (Or.inl h))

theorem disjoint_fits {a n b m c k e t : ℕ}
    (h : DisjointBlocks b m e t) (ha : Fits a n b m) (hc : Fits c k e t) :
    DisjointBlocks a n c k := by
  unfold DisjointBlocks at *
  unfold Fits at *
  omega

theorem fits_address {base count outer capacity address : ℕ}
    (h : Fits base count outer capacity)
    (ha : base ≤ address ∧ address < base + count) :
    outer ≤ address ∧ address < outer + capacity := by unfold Fits at h; omega

theorem square_capacity {m n : ℕ} (h : m ≤ n) : m * m ≤ n ^ 2 := by
  simpa only [pow_two] using Nat.mul_le_mul h h

theorem rectangle_capacity {m l n : ℕ} (hm : m ≤ n) (hl : l ≤ n) :
    m * l ≤ n ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hm hl

theorem Layout.frame_fits (L : Layout) (level : ℕ) (hl : level < L.order) :
    Fits (L.frame level) (L.entries ^ 2) L.frames (L.order * L.entries ^ 2) := by
  have h := Nat.mul_le_mul_right (L.entries ^ 2) hl
  unfold Fits Layout.frame
  constructor
  · omega
  · nlinarith

theorem Layout.frame_before_metadata (L : Layout) (level : ℕ) (hl : level < L.order) :
    L.frame level + L.entries ^ 2 ≤ L.metadata := by
  exact (L.frame_fits level hl).2

theorem Layout.frames_disjoint (L : Layout) (i j : ℕ) (h : i ≠ j) :
    DisjointBlocks (L.frame i) (L.entries ^ 2) (L.frame j) (L.entries ^ 2) := by
  rcases lt_or_gt_of_ne h with hij | hij
  · apply disjoint_of_end_le
    have hh := Nat.mul_le_mul_right (L.entries ^ 2) hij
    unfold Layout.frame
    nlinarith
  · apply disjoint_symm
    apply disjoint_of_end_le
    have hh := Nat.mul_le_mul_right (L.entries ^ 2) hij
    unfold Layout.frame
    nlinarith

theorem Layout.metadataCell_mem (L : Layout) (level field : ℕ)
    (hl : level < L.order) (hf : field < 4) :
    L.metadata ≤ L.metadataCell level field ∧ L.metadataCell level field < L.workA := by
  unfold Layout.metadataCell Layout.workA
  omega

theorem Layout.metadataCell_injective (L : Layout) (i j f g : ℕ)
    (hf : f < 4) (hg : g < 4)
    (h : L.metadataCell i f = L.metadataCell j g) : i = j ∧ f = g := by
  unfold Layout.metadataCell at h
  omega

theorem Layout.candidate_fits (L : Layout) (count j : ℕ) (hj : j < count) :
    Fits (L.candidate j) L.entries L.store (count * L.entries) := by
  have h := Nat.mul_le_mul_right L.entries hj
  unfold Fits Layout.candidate
  constructor
  · omega
  · nlinarith

theorem Layout.candidates_disjoint (L : Layout) (i j : ℕ) (h : i ≠ j) :
    DisjointBlocks (L.candidate i) L.entries (L.candidate j) L.entries := by
  rcases lt_or_gt_of_ne h with hij | hij
  · apply disjoint_of_end_le
    have hh := Nat.mul_le_mul_right L.entries hij
    unfold Layout.candidate
    nlinarith
  · apply disjoint_symm
    apply disjoint_of_end_le
    have hh := Nat.mul_le_mul_right L.entries hij
    unfold Layout.candidate
    nlinarith

#assert_trust kernel Layout.frames_disjoint
#assert_trust kernel Layout.candidates_disjoint
#assert_trust kernel Layout.metadataCell_injective
#print axioms Layout.frames_disjoint
#print axioms Layout.candidates_disjoint
end NLA.Proofs.TR04.TTMemoryLayout
