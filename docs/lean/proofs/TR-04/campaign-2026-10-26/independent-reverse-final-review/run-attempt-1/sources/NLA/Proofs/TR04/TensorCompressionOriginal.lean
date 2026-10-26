import NLA.Proofs.TR04.TensorCompressionMerge
import NLA.Proofs.TR04.TTCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Matrix

namespace NLA.Proofs.TR04.TensorFormat

/-- The first k actual mode sizes, without requiring any mode to be nonzero. -/
theorem take_ofFn_modes {d : ℕ} (n : Fin d → ℕ) (k : ℕ) (hk : k ≤ d) :
    (List.ofFn n).take k = List.ofFn (fun i : Fin k => n (Fin.castLE hk i)) := by
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
    cases d with
    | zero => omega
    | succ d =>
      have hk' : k ≤ d := by omega
      rw [List.ofFn_succ, List.take_succ_cons, List.ofFn_succ]
      congr 1
      rw [ih (fun i : Fin d => n i.succ) hk']
      apply congrArg List.ofFn
      funext i
      congr 1

/-- The remaining actual mode sizes after a prefix. -/
theorem drop_ofFn_modes {d : ℕ} (n : Fin d → ℕ) (k : ℕ) (hk : k ≤ d) :
    (List.ofFn n).drop k =
      List.ofFn (fun i : Fin (d - k) => n ⟨k + i.val, by omega⟩) := by
  induction k generalizing d with
  | zero =>
    simp only [List.drop_zero, Nat.sub_zero, Nat.zero_add]
  | succ k ih =>
    cases d with
    | zero => omega
    | succ d =>
      have hk' : k ≤ d := by omega
      rw [List.ofFn_succ, List.drop_succ_cons]
      simpa only [Nat.add_sub_add_right, Fin.succ_mk, Nat.add_assoc, Nat.add_comm 1, Fin.val_cast] using
        ih (fun i : Fin d => n i.succ) hk'

/-- Restrict the recursion-compatible product to a literal prefix vector. -/
def prefixIndexEquiv : {d : ℕ} → (n : Fin d → ℕ) → (k : ℕ) → (hk : k ≤ d) →
    Index ((modeList n).take k) ≃ ((i : Fin k) → Fin (n (Fin.castLE hk i)))
  | _, _, 0, _ => by
    change PUnit ≃ _
    exact
      { toFun := fun _ i => Fin.elim0 i,
        invFun := fun _ => PUnit.unit,
        left_inv := fun _ => Subsingleton.elim _ _,
        right_inv := fun _ => funext (fun i => Fin.elim0 i) }
  | 0, _, _ + 1, hk => False.elim (by omega)
  | d + 1, n, k + 1, hk =>
    (Equiv.prodCongr (Equiv.refl (Fin (n 0)))
      (prefixIndexEquiv (fun i : Fin d => n i.succ) k (by omega))).trans
        (Fin.consEquiv (fun i : Fin (k + 1) => Fin (n (Fin.castLE hk i))))

def suffixPositionZeroEquiv (d : ℕ) : Fin d ≃ {i : Fin d // 0 ≤ i.val} where
  toFun i := ⟨i, Nat.zero_le _⟩
  invFun i := i.1
  left_inv _ := rfl
  right_inv _ := rfl

def suffixPositionSuccEquiv (d k : ℕ) :
    {i : Fin d // k ≤ i.val} ≃ {i : Fin (d + 1) // k + 1 ≤ i.val} where
  toFun i := ⟨i.1.succ, by change k + 1 ≤ i.1.val + 1; have := i.2; omega⟩
  invFun i := ⟨⟨i.1.val - 1, by have := i.1.isLt; have := i.2; omega⟩,
    by change k ≤ i.1.val - 1; have := i.2; omega⟩
  left_inv i := by apply Subtype.ext; apply Fin.ext; simp
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    change i.1.val - 1 + 1 = i.1.val
    have := i.2
    omega

/-- Restrict the product to the actual suffix positions in the original mode vector. -/
def suffixIndexEquiv : {d : ℕ} → (n : Fin d → ℕ) → (k : ℕ) → (hk : k ≤ d) →
    Index ((modeList n).drop k) ≃ ((i : {i : Fin d // k ≤ i.val}) → Fin (n i.1))
  | d, n, 0, _ =>
    (vectorIndexEquiv n).trans
      (Equiv.piCongrLeft (fun i : {i : Fin d // 0 ≤ i.val} => Fin (n i.1))
        (suffixPositionZeroEquiv d))
  | 0, _, _ + 1, hk => False.elim (by omega)
  | d + 1, n, k + 1, hk =>
    (suffixIndexEquiv (fun i : Fin d => n i.succ) k (by omega)).trans
      (Equiv.piCongrLeft (fun i : {i : Fin (d + 1) // k + 1 ≤ i.val} => Fin (n i.1))
        (suffixPositionSuccEquiv d k))

 theorem prefix_join_coordinate {d : ℕ} (n : Fin d → ℕ) (k : ℕ) (hk : k ≤ d)
    (x : Index ((modeList n).take k)) (y : Index ((modeList n).drop k)) (i : Fin k) :
    vectorIndexEquiv n (joinIndex (modeList n) k x y) (Fin.castLE hk i) =
      prefixIndexEquiv n k hk x i := by
  induction k generalizing d with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    cases d with
    | zero => omega
    | succ d =>
      have hk' : k ≤ d := by omega
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [vectorIndexEquiv, prefixIndexEquiv, joinIndex, Fin.castLE, Fin.consEquiv, Fin.cons]
      · simpa [vectorIndexEquiv, prefixIndexEquiv, joinIndex, Fin.castLE, Fin.consEquiv, Fin.cons] using
          ih (fun i : Fin d => n i.succ) hk' x.2 y i

 theorem suffix_join_coordinate {d : ℕ} (n : Fin d → ℕ) (k : ℕ) (hk : k ≤ d)
    (x : Index ((modeList n).take k)) (y : Index ((modeList n).drop k))
    (i : {i : Fin d // k ≤ i.val}) :
    vectorIndexEquiv n (joinIndex (modeList n) k x y) i.1 =
      suffixIndexEquiv n k hk y i := by
  induction k generalizing d with
  | zero =>
    change Index (modeList n) at y
    have hz := joinIndex_zero (modeList n) x y
    rw [hz]
    let q : Fin d := i.1
    have he : suffixPositionZeroEquiv d q = i := rfl
    rw [← he]
    rw [suffixIndexEquiv, Equiv.trans_apply]
    exact (Equiv.piCongrLeft_apply_apply
      (fun i : {i : Fin d // 0 ≤ i.val} => Fin (n i.1))
      (suffixPositionZeroEquiv d) ((vectorIndexEquiv n) y) q).symm

  | succ k ih =>
    cases d with
    | zero => omega
    | succ d =>
      let q : {i : Fin d // k ≤ i.val} := ⟨⟨i.1.val - 1, by have := i.1.isLt; have := i.2; omega⟩,
        by change k ≤ i.1.val - 1; have := i.2; omega⟩
      have he : suffixPositionSuccEquiv d k q = i := by
        apply Subtype.ext
        apply Fin.ext
        dsimp [q, suffixPositionSuccEquiv]
        have := i.2
        omega
      rw [← he]
      change vectorIndexEquiv (fun i : Fin d => n i.succ)
        (joinIndex (modeList (fun i : Fin d => n i.succ)) k x.2 y) q.1 =
        (Equiv.piCongrLeft (fun i : {i : Fin (d + 1) // k + 1 ≤ i.val} => Fin (n i.1))
          (suffixPositionSuccEquiv d k))
            ((suffixIndexEquiv (fun i : Fin d => n i.succ) k (by omega)) y)
              (suffixPositionSuccEquiv d k q)
      rw [Equiv.piCongrLeft_apply_apply]
      exact ih (fun i : Fin d => n i.succ) (by omega) x.2 y q

theorem originalCut_le (S : NLA.Computation.TensorTrainApproximation.Shape)
    (j : NLA.Computation.TensorTrainApproximation.Cut S) : j.val + 1 ≤ S.order := by
  have := j.isLt
  have := S.order_ge
  omega

def originalRowPositionEquiv (S : NLA.Computation.TensorTrainApproximation.Shape)
    (j : NLA.Computation.TensorTrainApproximation.Cut S) :
    Fin (j.val + 1) ≃ {i : Fin S.order // i.val ≤ j.val} where
  toFun i := ⟨Fin.castLE (originalCut_le S j) i, by have := i.isLt; change i.val ≤ j.val; omega⟩
  invFun i := ⟨i.1.val, by have := i.2; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

def originalColPositionEquiv (S : NLA.Computation.TensorTrainApproximation.Shape)
    (j : NLA.Computation.TensorTrainApproximation.Cut S) :
    {i : Fin S.order // j.val + 1 ≤ i.val} ≃ {i : Fin S.order // j.val < i.val} where
  toFun i := ⟨i.1, by have := i.2; omega⟩
  invFun i := ⟨i.1, by have := i.2; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

def originalRowEquiv (S : NLA.Computation.TensorTrainApproximation.Shape)
    (j : NLA.Computation.TensorTrainApproximation.Cut S) :
    Index ((modeList S.mode).take (j.val + 1)) ≃
      NLA.Computation.TensorTrainApproximation.RowIndex S j :=
  (prefixIndexEquiv S.mode (j.val + 1) (originalCut_le S j)).trans
    (Equiv.piCongrLeft (fun i : {i : Fin S.order // i.val ≤ j.val} => Fin (S.mode i.1))
      (originalRowPositionEquiv S j))

def originalColEquiv (S : NLA.Computation.TensorTrainApproximation.Shape)
    (j : NLA.Computation.TensorTrainApproximation.Cut S) :
    Index ((modeList S.mode).drop (j.val + 1)) ≃
      NLA.Computation.TensorTrainApproximation.ColIndex S j :=
  (suffixIndexEquiv S.mode (j.val + 1) (originalCut_le S j)).trans
    (Equiv.piCongrLeft (fun i : {i : Fin S.order // j.val < i.val} => Fin (S.mode i.1))
      (originalColPositionEquiv S j))

/-- Exact coordinate agreement with the original published cut concatenation. -/
theorem original_join (S : NLA.Computation.TensorTrainApproximation.Shape)
    (j : NLA.Computation.TensorTrainApproximation.Cut S)
    (x : Index ((modeList S.mode).take (j.val + 1)))
    (y : Index ((modeList S.mode).drop (j.val + 1))) :
    vectorIndexEquiv S.mode (joinIndex (modeList S.mode) (j.val + 1) x y) =
      NLA.Computation.TensorTrainApproximation.join S j
        (originalRowEquiv S j x) (originalColEquiv S j y) := by
  funext i
  by_cases hi : i.val ≤ j.val
  · let q : Fin (j.val + 1) := ⟨i.val, by omega⟩
    have he : originalRowPositionEquiv S j q = ⟨i, hi⟩ := by apply Subtype.ext; apply Fin.ext; rfl
    rw [NLA.Computation.TensorTrainApproximation.join, dif_pos hi]
    change _ = (originalRowEquiv S j x) (originalRowPositionEquiv S j q)
    change _ = (Equiv.piCongrLeft
      (fun i : {i : Fin S.order // i.val ≤ j.val} => Fin (S.mode i.1))
        (originalRowPositionEquiv S j))
          ((prefixIndexEquiv S.mode (j.val + 1) (originalCut_le S j)) x)
            (originalRowPositionEquiv S j q)
    rw [Equiv.piCongrLeft_apply_apply]
    exact prefix_join_coordinate S.mode (j.val + 1) (originalCut_le S j) x y q
  · let q : {i : Fin S.order // j.val + 1 ≤ i.val} := ⟨i, by omega⟩
    have he : originalColPositionEquiv S j q = ⟨i, Nat.lt_of_not_ge hi⟩ := rfl
    rw [NLA.Computation.TensorTrainApproximation.join, dif_neg hi]
    change _ = (originalColEquiv S j y) (originalColPositionEquiv S j q)
    change _ = (Equiv.piCongrLeft
      (fun i : {i : Fin S.order // j.val < i.val} => Fin (S.mode i.1))
        (originalColPositionEquiv S j))
          ((suffixIndexEquiv S.mode (j.val + 1) (originalCut_le S j)) y)
            (originalColPositionEquiv S j q)
    rw [Equiv.piCongrLeft_apply_apply]
    exact suffix_join_coordinate S.mode (j.val + 1) (originalCut_le S j) x y q

/-- The auxiliary unfolding is the literal original matrix reindexed by
proved row and column bijections; it is not an unrelated rank surrogate. -/
theorem unfold_original (S : NLA.Computation.TensorTrainApproximation.Shape)
    (j : NLA.Computation.TensorTrainApproximation.Cut S)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S) :
    unfold (modeList S.mode) (originalTensorLinearEquiv S A) (j.val + 1) =
      (NLA.Computation.TensorTrainApproximation.Unfold S A j).submatrix
        (originalRowEquiv S j) (originalColEquiv S j) := by
  ext x y
  exact congrArg A (original_join S j x y)

theorem rank_unfold_original (S : NLA.Computation.TensorTrainApproximation.Shape)
    (j : NLA.Computation.TensorTrainApproximation.Cut S)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S) :
    Matrix.rank (unfold (modeList S.mode) (originalTensorLinearEquiv S A) (j.val + 1)) =
      Matrix.rank (NLA.Computation.TensorTrainApproximation.Unfold S A j) := by
  rw [unfold_original]
  exact Matrix.rank_submatrix _ (originalRowEquiv S j) (originalColEquiv S j)

def originalRanks (S : NLA.Computation.TensorTrainApproximation.Shape)
    (r : NLA.Computation.TensorTrainApproximation.Ranks S) (j : ℕ) : ℕ :=
  if h : j < S.order - 1 then r ⟨j, h⟩ else 0

theorem original_feasible_iff (S : NLA.Computation.TensorTrainApproximation.Shape)
    (r : NLA.Computation.TensorTrainApproximation.Ranks S)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S) :
    NLA.Computation.TensorTrainApproximation.Feasible S r A ↔
      RankFeasible (modeList S.mode) (originalRanks S r) (originalTensorLinearEquiv S A) := by
  constructor
  · intro h j hj hlen
    rw [length_modeList] at hlen
    have hcut : j - 1 < S.order - 1 := by omega
    let q : NLA.Computation.TensorTrainApproximation.Cut S := ⟨j - 1, hcut⟩
    have heq : j = q.val + 1 := by dsimp [q]; omega
    rw [heq, rank_unfold_original]
    simpa [originalRanks, q, hcut] using h q
  · intro h j
    have hlen : j.val + 1 < (modeList S.mode).length := by
      rw [length_modeList]
      have := j.isLt
      have := S.order_ge
      omega
    have hh := h (j.val + 1) (by omega) hlen
    rw [rank_unfold_original] at hh
    simpa [originalRanks, j.isLt] using hh

#assert_trust kernel prefixIndexEquiv
#assert_trust kernel suffixIndexEquiv
#assert_trust kernel prefix_join_coordinate
#assert_trust kernel suffix_join_coordinate
#assert_trust kernel originalRowEquiv
#assert_trust kernel originalColEquiv
#assert_trust kernel original_join
#assert_trust kernel unfold_original
#assert_trust kernel rank_unfold_original
#assert_trust kernel original_feasible_iff
#print axioms original_feasible_iff
#assert_trust kernel take_ofFn_modes
#assert_trust kernel drop_ofFn_modes
end NLA.Proofs.TR04.TensorFormat
