import NLA.Proofs.TR04.MachineMatrixMultiplyCallable
import NLA.Proofs.TR04.TensorCompressionRadixDecode
import NLA.Proofs.TR04.TensorCompressionRadixSVD

/-! Literal tensor/frame memory representations at the actual explicit radix
addresses, including the physical identity of a leading-mode merge. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04.TensorFormat
open NLA.Computation.SVDMachine

def StoresTensor (memory : ℕ → ℝ) (base : ℕ) (ns : List ℕ) (A : Tensor ns) : Prop :=
  ∀ x : Index ns, memory (base + radixOffset ns x) = A x

def StoresFrame {m q : ℕ} (memory : ℕ → ℝ) (base stride : ℕ)
    (Q : Matrix (Fin m) (Fin q) ℝ) : Prop :=
  ∀ i k, memory (base + i.val * stride + k.val) = Q i k

theorem tensor_suffixSize_eq_prod (ns : List ℕ) : suffixSize ns = ns.prod := card_index ns

theorem radixOffset_radixSuffixEquiv (ns : List ℕ) (j : Fin (suffixSize ns)) :
    radixOffset ns (radixSuffixEquiv ns j) = j.val := by
  have h := radixSuffixEquiv_symm_val ns (radixSuffixEquiv ns j)
  simpa only [Equiv.symm_apply_apply] using h.symm

theorem storesTensor_iff_flat (memory : ℕ → ℝ) (base : ℕ) (ns : List ℕ) (A : Tensor ns) :
    StoresTensor memory base ns A ↔
      ∀ i : Fin ns.prod, memory (base + i.val) = A (radixIndexEquiv ns i) := by
  constructor
  · intro h i
    have hi := radixIndexEquiv_symm_val ns (radixIndexEquiv ns i)
    have hi' : radixOffset ns (radixIndexEquiv ns i) = i.val := by
      simpa only [Equiv.symm_apply_apply] using hi.symm
    have hh := h (radixIndexEquiv ns i)
    rwa [hi'] at hh
  · intro h x
    simpa only [radixIndexEquiv_decode_encode] using h ⟨radixOffset ns x, radixOffset_lt ns x⟩

theorem storesTensor_readMatrix_iff {m : ℕ} {ns : List ℕ}
    (memory : ℕ → ℝ) (base : ℕ) (A : Tensor (m :: ns)) :
    StoresTensor memory base (m :: ns) A ↔
      readMatrix memory m (suffixSize ns) base = radixDenseFirst A := by
  constructor
  · intro h
    ext i j
    change memory (base + i.val * suffixSize ns + j.val) = A (i, radixSuffixEquiv ns j)
    have he : base + i.val * suffixSize ns + j.val =
        base + radixOffset (m :: ns) (i, radixSuffixEquiv ns j) := by
      simp only [radixOffset, tensor_suffixSize_eq_prod, radixOffset_radixSuffixEquiv, Nat.add_assoc]
    rw [he]
    exact h _
  · intro h x
    rcases x with ⟨i, x⟩
    let j := (radixSuffixEquiv ns).symm x
    have he := congrFun (congrFun h i) j
    change memory (base + i.val * suffixSize ns + j.val) = A (i, radixSuffixEquiv ns j) at he
    have hj : j.val = radixOffset ns x := radixSuffixEquiv_symm_val ns x
    simpa only [j, Equiv.apply_symm_apply, hj, tensor_suffixSize_eq_prod, radixOffset, Nat.add_assoc] using he

theorem radixDenseFirst_actFirst {m q : ℕ} {ns : List ℕ}
    (M : Matrix (Fin q) (Fin m) ℝ) (A : Tensor (m :: ns)) :
    radixDenseFirst (actFirst M A) = M * radixDenseFirst A := rfl

theorem radixOffset_merge_indices (k n : ℕ) (ns : List ℕ)
    (i : Fin k) (j : Fin n) (x : Index ns) :
    radixOffset ((k * n) :: ns) (finProdFinEquiv (i, j), x) =
      radixOffset (k :: n :: ns) (i, j, x) := by
  change (j.val + n * i.val) * ns.prod + radixOffset ns x =
    i.val * (n * ns.prod) + (j.val * ns.prod + radixOffset ns x)
  ring

theorem storesTensor_merge_iff (memory : ℕ → ℝ) (base k n : ℕ) (ns : List ℕ)
    (A : Tensor (k :: n :: ns)) :
    StoresTensor memory base (k :: n :: ns) A ↔
      StoresTensor memory base ((k * n) :: ns) (merge k n ns A) := by
  constructor
  · intro h x
    rcases x with ⟨ij, x⟩
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective ij
    rw [radixOffset_merge_indices, merge_apply]
    exact h (i, j, x)
  · intro h x
    rcases x with ⟨i, j, x⟩
    have he := h (finProdFinEquiv (i, j), x)
    rwa [radixOffset_merge_indices, merge_apply] at he

theorem storesTensor_unmerge_iff (memory : ℕ → ℝ) (base k n : ℕ) (ns : List ℕ)
    (A : Tensor ((k * n) :: ns)) :
    StoresTensor memory base ((k * n) :: ns) A ↔
      StoresTensor memory base (k :: n :: ns) ((merge k n ns).symm A) := by
  simpa only [LinearEquiv.apply_symm_apply] using
    (storesTensor_merge_iff memory base k n ns ((merge k n ns).symm A)).symm

theorem StoresTensor.memory_eq {memory memory' : ℕ → ℝ} {base : ℕ} {ns : List ℕ} {A : Tensor ns}
    (h : StoresTensor memory base ns A)
    (he : ∀ a, base ≤ a ∧ a < base + ns.prod → memory' a = memory a) :
    StoresTensor memory' base ns A := by
  intro x
  rw [he _ (by have hx := radixOffset_lt ns x; omega)]
  exact h x

theorem storesFrame_dense_iff {m q : ℕ} (memory : ℕ → ℝ) (base : ℕ)
    (Q : Matrix (Fin m) (Fin q) ℝ) :
    StoresFrame memory base q Q ↔ readMatrix memory m q base = Q := by
  constructor
  · intro h
    ext i k
    exact h i k
  · intro h i k
    exact congrFun (congrFun h i) k

theorem storesFrame_prefix {m q : ℕ} (memory : ℕ → ℝ) (base : ℕ)
    (U : Matrix (Fin m) (Fin m) ℝ) (hq : q ≤ m)
    (hU : readMatrix memory m m base = U) :
    StoresFrame memory base m (U.submatrix id (Fin.castLE hq)) := by
  intro i k
  exact congrFun (congrFun hU i) (Fin.castLE hq k)

theorem StoresFrame.memory_eq {m q : ℕ} {memory memory' : ℕ → ℝ} {base stride : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} (h : StoresFrame memory base stride Q) (hq : q ≤ stride)
    (he : ∀ a, base ≤ a ∧ a < base + m * stride → memory' a = memory a) :
    StoresFrame memory' base stride Q := by
  intro i k
  have hi := matrix_offset_lt i (Fin.castLE hq k)
  change i.val * stride + k.val < m * stride at hi
  rw [he _ (by omega)]
  exact h i k

theorem storesTensor_original (S : NLA.Computation.TensorTrainApproximation.Shape)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S) (memory : ℕ → ℝ) (base : ℕ)
    (h : ∀ x, memory (base + NLA.Computation.TensorTrainApproximation.Offset S x) = A x) :
    StoresTensor memory base (modeList S.mode) (originalTensorLinearEquiv S A) := by
  intro x
  have ho := original_radixOffset S (vectorIndexEquiv S.mode x)
  rw [Equiv.symm_apply_apply] at ho
  change memory (base + radixOffset (modeList S.mode) x) = A (vectorIndexEquiv S.mode x)
  rw [ho]
  exact h _

#assert_trust kernel StoresTensor
#assert_trust kernel StoresFrame
#assert_trust kernel storesTensor_iff_flat
#assert_trust kernel storesTensor_readMatrix_iff
#assert_trust kernel radixDenseFirst_actFirst
#assert_trust kernel storesTensor_merge_iff
#assert_trust kernel storesTensor_unmerge_iff
#assert_trust kernel StoresTensor.memory_eq
#assert_trust kernel storesFrame_prefix
#assert_trust kernel StoresFrame.memory_eq
#assert_trust kernel storesTensor_original
#print axioms storesTensor_readMatrix_iff
end NLA.Proofs.TR04.TensorFormat
