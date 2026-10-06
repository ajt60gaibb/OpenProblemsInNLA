/- Exact original-coordinate embedding of a selected-block inverse truncation.
The exact contract was approved before implementation in reviews/.
-/
import NLA.IE06.SelectedBlockElimination
import NLA.IE06.EliminationSmoothing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
noncomputable section
open Matrix WithLp
open scoped BigOperators
namespace NLA.IE06.SelectedBlockTruncation
open GaussianPivotConditioning SelectedBlockElimination EliminationSmoothing

/-- The literal injection of the selected original row coordinates. -/
def coordinateEmbedding {n t : ℕ} (π : Fin t ↪ Fin n) : Matrix (Fin n) (Fin t) ℝ :=
  fun j a => if j = π a then 1 else 0

theorem coordinateEmbedding_orthonormal {n t : ℕ} (π : Fin t ↪ Fin n) :
    (coordinateEmbedding π)ᴴ * coordinateEmbedding π = 1 := by
  ext a b
  simp [coordinateEmbedding,Matrix.mul_apply,Matrix.one_apply,π.injective.eq_iff,eq_comm]

theorem mul_embedding_conjTranspose {n t m : ℕ} (π : Fin t ↪ Fin n)
    (C : Matrix (Fin m) (Fin t) ℝ) (i : Fin m) (j : Fin n) :
    (C * (coordinateEmbedding π)ᴴ) i j =
      ∑ a : Fin t, C i a * (if j = π a then 1 else 0) := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,coordinateEmbedding]

/-- Active original rows restricted to the first t original columns. -/
def activePrefixRows {n t : ℕ} (ht : t ≤ n) (A : Mat n) : Matrix (Fin n) (Fin t) ℝ :=
  fun i a => if t ≤ i.val then prefixRows ht A (rowLabels (firstPath A) t i) a else 0

def activeIdentityRows {n t : ℕ} (_ht : t ≤ n) (A : Mat n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if t ≤ i.val then (if j = rowLabels (firstPath A) t i then 1 else 0) else 0

def retainedRows {n t : ℕ} (ht : t ≤ n) (A : Mat n) (Z : Matrix (Fin t) (Fin t) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  activeIdentityRows ht A - (activePrefixRows ht A * Z) * (coordinateEmbedding (pivotOrder ht A))ᴴ

def discardedRows {n t q : ℕ} (ht : t ≤ n) (A : Mat n) (H : Matrix (Fin t) (Fin q) ℝ) :
    Matrix (Fin n) (Fin q) ℝ := -(activePrefixRows ht A * H)

def discardedFrame {n t q : ℕ} (π : Fin t ↪ Fin n) (V : Matrix (Fin t) (Fin q) ℝ) :
    Matrix (Fin n) (Fin q) ℝ := coordinateEmbedding π * V

theorem discardedFrame_orthonormal {n t q : ℕ} (π : Fin t ↪ Fin n)
    (V : Matrix (Fin t) (Fin q) ℝ) (hV : Vᴴ * V = 1) :
    (discardedFrame π V)ᴴ * discardedFrame π V = 1 := by
  simp only [discardedFrame,Matrix.conjTranspose_mul]
  calc
    _ = Vᴴ * ((coordinateEmbedding π)ᴴ * coordinateEmbedding π) * V := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [coordinateEmbedding_orthonormal,Matrix.mul_one,hV]

theorem activePrefixRows_mul_apply {n t q : ℕ} (ht : t ≤ n) (A : Mat n)
    (Z : Matrix (Fin t) (Fin q) ℝ) (i : Fin n) (a : Fin q) :
    (activePrefixRows ht A * Z) i a =
      if t ≤ i.val then (prefixRows ht A (rowLabels (firstPath A) t i) ᵥ* Z) a else 0 := by
  by_cases hi : t ≤ i.val
  · simp [Matrix.mul_apply,activePrefixRows,hi,Matrix.vecMul,dotProduct]
  · simp [Matrix.mul_apply,activePrefixRows,hi]

theorem retainedRows_apply {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (Z : Matrix (Fin t) (Fin t) ℝ) (i j : Fin n) :
    retainedRows ht A Z i j = if t ≤ i.val then
      (if j = rowLabels (firstPath A) t i then 1 else 0) -
      ∑ a : Fin t, (prefixRows ht A (rowLabels (firstPath A) t i) ᵥ* Z) a *
        (if j = pivotOrder ht A a then 1 else 0) else 0 := by
  simp only [retainedRows,Matrix.sub_apply,mul_embedding_conjTranspose,activePrefixRows_mul_apply]
  by_cases hi : t ≤ i.val <;> simp [activeIdentityRows,hi]

theorem discardedRows_apply {n t q : ℕ} (ht : t ≤ n) (A : Mat n)
    (H : Matrix (Fin t) (Fin q) ℝ) (i : Fin n) (a : Fin q) :
    discardedRows ht A H i a = if t ≤ i.val then
      -(prefixRows ht A (rowLabels (firstPath A) t i) ᵥ* H) a else 0 := by
  simp only [discardedRows,Matrix.neg_apply,activePrefixRows_mul_apply]
  split_ifs <;> simp

theorem eliminationRows_eq_full_inverse {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (hp : PrefixNonzero ht A) :
    Matrix.of (eliminationRows A (firstPath A) t) =
      retainedRows ht A (selectedBlock ht (pivotOrder ht A) A)⁻¹ := by
  ext i j
  rw [retainedRows_apply]
  by_cases hi : t ≤ i.val
  · rw [if_pos hi]
    exact row_eq_selected_inverse_of_prefix ht A hp i hi j
  · rw [if_neg hi]
    exact eliminationRows_inactive A (firstPath A) i j (by omega)

/-- The actual padded E=X+YQ^T, without any norm assumption on H or Y. -/
theorem eliminationRows_decomposition {n t q : ℕ} (ht : t ≤ n) (A : Mat n)
    (hp : PrefixNonzero ht A) (Z : Matrix (Fin t) (Fin t) ℝ)
    (H V : Matrix (Fin t) (Fin q) ℝ)
    (hT : (selectedBlock ht (pivotOrder ht A) A)⁻¹ = Z + H * Vᴴ) :
    Matrix.of (eliminationRows A (firstPath A) t) =
      retainedRows ht A Z + discardedRows ht A H * (discardedFrame (pivotOrder ht A) V)ᴴ := by
  rw [eliminationRows_eq_full_inverse ht A hp]
  simp only [retainedRows,discardedRows,discardedFrame,hT,Matrix.mul_add,Matrix.add_mul,
    Matrix.neg_mul,Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  abel

/-- Exact active-row energy of the retained component, in original coordinates. -/
theorem retainedRows_rowNorm_sq {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (Z : Matrix (Fin t) (Fin t) ℝ) (i : Fin n) (hi : t ≤ i.val) :
    rowNorm (retainedRows ht A Z) i ^ 2 =
      1 + ‖(toLp 2 (prefixRows ht A (rowLabels (firstPath A) t i) ᵥ* Z) :
        EuclideanSpace ℝ (Fin t))‖^2 := by
  rw [EliminationSmoothing.rowNorm_sq,EuclideanSpace.real_norm_sq_eq]
  simp only [retainedRows_apply,hi,if_true]
  exact selected_embedding_sq (pivotOrder ht A) (rowLabels (firstPath A) t i)
    (active_label_not_selected ht A i hi) _

theorem retainedRows_inactive {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (Z : Matrix (Fin t) (Fin t) ℝ) (i : Fin n) (hi : i.val < t) :
    retainedRows ht A Z i = 0 := by
  funext j
  simp [retainedRows_apply,not_le.mpr hi]

theorem discardedRows_inactive {n t q : ℕ} (ht : t ≤ n) (A : Mat n)
    (H : Matrix (Fin t) (Fin q) ℝ) (i : Fin n) (hi : i.val < t) :
    discardedRows ht A H i = 0 := by
  funext a
  simp [discardedRows_apply,not_le.mpr hi]

#assert_trust kernel coordinateEmbedding
#print axioms coordinateEmbedding
#assert_trust kernel coordinateEmbedding_orthonormal
#print axioms coordinateEmbedding_orthonormal
#assert_trust kernel mul_embedding_conjTranspose
#print axioms mul_embedding_conjTranspose
#assert_trust kernel activePrefixRows
#print axioms activePrefixRows
#assert_trust kernel activeIdentityRows
#print axioms activeIdentityRows
#assert_trust kernel retainedRows
#print axioms retainedRows
#assert_trust kernel discardedRows
#print axioms discardedRows
#assert_trust kernel discardedFrame
#print axioms discardedFrame
#assert_trust kernel discardedFrame_orthonormal
#print axioms discardedFrame_orthonormal
#assert_trust kernel activePrefixRows_mul_apply
#print axioms activePrefixRows_mul_apply
#assert_trust kernel retainedRows_apply
#print axioms retainedRows_apply
#assert_trust kernel discardedRows_apply
#print axioms discardedRows_apply
#assert_trust kernel eliminationRows_eq_full_inverse
#print axioms eliminationRows_eq_full_inverse
#assert_trust kernel eliminationRows_decomposition
#print axioms eliminationRows_decomposition
#assert_trust kernel retainedRows_rowNorm_sq
#print axioms retainedRows_rowNorm_sq
#assert_trust kernel retainedRows_inactive
#print axioms retainedRows_inactive
#assert_trust kernel discardedRows_inactive
#print axioms discardedRows_inactive

end NLA.IE06.SelectedBlockTruncation
