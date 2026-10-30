import NLA.Proofs.TR04.TTMemoryLayoutProtection

/-! Polynomial address bounds for the concrete allocation, including the exact
original-format input-data base and four metadata cells per recursive level. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.TR04.TTMemoryLayout
open NLA.Computation.SVDMachine
open NLA.Computation.TensorTrainApproximation

 theorem Layout.endAddress_eq (L : Layout) (count : ℕ) :
    L.endAddress count = L.input + (L.order + 3) * L.entries ^ 2 +
      (count + 5) * L.entries + 4 * L.order := by
  unfold Layout.endAddress Layout.store Layout.workB Layout.workA Layout.metadata
    Layout.frames Layout.childV Layout.childSigma Layout.firstV Layout.firstSigma Layout.firstU
  ring

 theorem Layout.store_le_endAddress (L : Layout) (count : ℕ) :
    L.store ≤ L.endAddress count := by unfold Layout.endAddress; omega

 theorem Layout.metadata_before_store (L : Layout) : L.metadata + 4 * L.order ≤ L.store := by
  unfold Layout.store Layout.workB Layout.workA
  omega

 theorem Layout.workA_before_store (L : Layout) : L.workA + L.entries ≤ L.store := by
  unfold Layout.store Layout.workB
  omega

 theorem Layout.workB_before_store (L : Layout) : L.workB + L.entries ≤ L.store := by
  rfl

 theorem Layout.prefix_address_lt_end (L : Layout) (count base length address : ℕ)
    (hb : base + length ≤ L.store) (ha : base ≤ address ∧ address < base + length) :
    address < L.endAddress count := by
  have h := L.store_le_endAddress count
  omega

 theorem Layout.frame_address_lt_end (L : Layout) (count level address : ℕ)
    (hl : level < L.order)
    (ha : L.frame level ≤ address ∧ address < L.frame level + L.entries ^ 2) :
    address < L.endAddress count := by
  have hf := L.frame_before_workA level hl
  have hw := L.workA_before_store
  exact L.prefix_address_lt_end count _ _ address (by omega) ha

 theorem Layout.metadata_address_lt_end (L : Layout) (count level field : ℕ)
    (hl : level < L.order) (hf : field < 4) :
    L.metadataCell level field < L.endAddress count := by
  have h := L.metadataCell_mem level field hl hf
  have hw := L.workA_before_store
  have he := L.store_le_endAddress count
  omega

 theorem Layout.candidate_address_lt_end (L : Layout) (count j address : ℕ)
    (hj : j < count)
    (ha : L.candidate j ≤ address ∧ address < L.candidate j + L.entries) :
    address < L.endAddress count := by
  have h := fits_address (L.candidate_fits count j hj) ha
  exact h.2

 theorem Layout.endAddress_le_cubic (L : Layout) (count size : ℕ)
    (hd : L.order ≤ size) (hn : L.entries ≤ size) (hk : count ≤ L.entries + 1) :
    L.endAddress count ≤ 20 * (size + 1) ^ 3 := by
  have hb : L.input ≤ 2 * size := by
    unfold Layout.input
    exact (Nat.sub_le _ _).trans (Nat.mul_le_mul_left 2 hd)
  have hn2 : L.entries ^ 2 ≤ size ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hn hn
  have hsq : (L.order + 3) * L.entries ^ 2 ≤ (size + 3) * size ^ 2 :=
    Nat.mul_le_mul (by omega) hn2
  have hk' : (count + 5) * L.entries ≤ (size + 6) * size :=
    Nat.mul_le_mul (by omega) hn
  have hd' := Nat.mul_le_mul_left 4 hd
  rw [L.endAddress_eq]
  calc
    L.input + (L.order + 3) * L.entries ^ 2 + (count + 5) * L.entries + 4 * L.order
      ≤ 2 * size + (size + 3) * size ^ 2 + (size + 6) * size + 4 * size := by omega
    _ ≤ 20 * (size + 1) ^ 3 := by nlinarith

 theorem ofShape_input (S : Shape) : (ofShape S).input = 2 * S.order - 1 := rfl

 theorem ofShape_endAddress_le_size (S : Shape) (r : Ranks S) (count : ℕ)
    (hk : count ≤ DenseSize S + 1) :
    (ofShape S).endAddress count ≤ 20 * (Size S r + 1) ^ 3 := by
  apply Layout.endAddress_le_cubic
  · exact (NLA.Proofs.TR04.shape_order_le_denseSize S).trans
      (NLA.Proofs.TR04.shape_denseSize_le_size S r)
  · exact NLA.Proofs.TR04.shape_denseSize_le_size S r
  · exact hk

 theorem ofShape_allocated_address_lt_size (S : Shape) (r : Ranks S) (count address : ℕ)
    (hk : count ≤ DenseSize S + 1) (ha : address < (ofShape S).endAddress count) :
    address < 20 * (Size S r + 1) ^ 3 :=
  ha.trans_le (ofShape_endAddress_le_size S r count hk)

/-- Natural metadata, stored as rows, compressed width, suffix columns and stride.
Bounds are explicit; rectangular products are separate invariants. -/
structure StageMetadata where
  rows : ℕ
  width : ℕ
  cols : ℕ
  stride : ℕ

def StageMetadata.value (M : StageMetadata) (field : ℕ) : ℕ :=
  if field = 0 then M.rows else if field = 1 then M.width else
  if field = 2 then M.cols else M.stride

def StageMetadata.Bounded (M : StageMetadata) (bound : ℕ) : Prop :=
  M.rows ≤ bound ∧ M.width ≤ bound ∧ M.cols ≤ bound ∧ M.stride ≤ bound

 theorem StageMetadata.value_le (M : StageMetadata) (bound field : ℕ)
    (h : M.Bounded bound) : M.value field ≤ bound := by
  unfold StageMetadata.value StageMetadata.Bounded at *
  split_ifs <;> omega

 theorem StageMetadata.frame_capacity (M : StageMetadata) (bound : ℕ)
    (h : M.Bounded bound) : M.rows * M.width ≤ bound ^ 2 :=
  rectangle_capacity h.1 h.2.1

 theorem StageMetadata.original_value_le_size (S : Shape) (r : Ranks S)
    (M : StageMetadata) (h : M.Bounded (DenseSize S)) (field : ℕ) :
    M.value field ≤ Size S r :=
  (M.value_le _ field h).trans (NLA.Proofs.TR04.shape_denseSize_le_size S r)

#assert_trust kernel Layout.endAddress_eq
#assert_trust kernel Layout.endAddress_le_cubic
#assert_trust kernel ofShape_endAddress_le_size
#assert_trust kernel ofShape_allocated_address_lt_size
#assert_trust kernel StageMetadata.frame_capacity
#print axioms Layout.endAddress_le_cubic
#print axioms ofShape_endAddress_le_size
end NLA.Proofs.TR04.TTMemoryLayout
