import NLA.Proofs.TR04.SVDFrameSpace

/-! Explicit selected column indices. The frame itself uses only the prefix,
addition and cyclic remainder, with no enumeration of a finite subtype. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04.SVD

def cyclicColumnIndex {p : ℕ} (h t : ℕ) [NeZero t] (ht : h + t ≤ p)
    (s : ℕ) (hst : s ≤ t) (j : Fin t) (k : Fin (h + s)) : Fin p :=
  if hk : k.val < h then ⟨k.val, by omega⟩
  else tieEmbedding h t ht (j + ⟨k.val - h, by omega⟩)

theorem cyclicColumnIndex_val {p h t : ℕ} [NeZero t] (ht : h + t ≤ p)
    (s : ℕ) (hst : s ≤ t) (j : Fin t) (k : Fin (h + s)) :
    (cyclicColumnIndex h t ht s hst j k).val =
      if k.val < h then k.val else h + ((j.val + (k.val - h)) % t) := by
  unfold cyclicColumnIndex
  split_ifs <;> rfl

theorem cyclicColumnIndex_injective {p h t : ℕ} [NeZero t] (ht : h + t ≤ p)
    (s : ℕ) (hst : s ≤ t) (j : Fin t) :
    Function.Injective (cyclicColumnIndex h t ht s hst j) := by
  intro a b he
  by_cases ha : a.val < h <;> by_cases hb : b.val < h
  · apply Fin.ext
    simpa only [cyclicColumnIndex, dif_pos ha, dif_pos hb] using congrArg Fin.val he
  · have hh := congrArg Fin.val he
    simp only [cyclicColumnIndex, dif_pos ha, dif_neg hb, tieEmbedding] at hh
    change a.val = h + (j + (⟨b.val - h, by omega⟩ : Fin t)).val at hh
    have hle : h ≤ a.val := by rw [hh]; exact Nat.le_add_right _ _
    exact False.elim (Nat.not_le_of_gt ha hle)
  · have hh := congrArg Fin.val he
    simp only [cyclicColumnIndex, dif_neg ha, dif_pos hb, tieEmbedding] at hh
    change h + (j + (⟨a.val - h, by omega⟩ : Fin t)).val = b.val at hh
    have hle : h ≤ b.val := by rw [← hh]; exact Nat.le_add_right _ _
    exact False.elim (Nat.not_le_of_gt hb hle)
  · simp only [cyclicColumnIndex, dif_neg ha, dif_neg hb] at he
    have hi := add_left_cancel (tieEmbedding_injective ht he)
    have hv := congrArg Fin.val hi
    apply Fin.ext
    dsimp at hv
    omega

theorem cyclicColumnIndex_mem {p h t : ℕ} [NeZero t] (ht : h + t ≤ p)
    (s : ℕ) (hst : s ≤ t) (j : Fin t) (k : Fin (h + s)) :
    cyclicColumnIndex h t ht s hst j k ∈ tieSelection h t ht s j := by
  classical
  by_cases hk : k.val < h
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨⟨k.val, hk⟩, Finset.mem_univ _, ?_⟩
    simp only [cyclicColumnIndex, dif_pos hk]
    rfl
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨j + ⟨k.val - h, by omega⟩, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [cyclicWindow, add_sub_cancel_left]
      omega
    · simp only [cyclicColumnIndex, dif_neg hk]

theorem cyclicColumnIndex_surjective {p h t : ℕ} [NeZero t] (ht : h + t ≤ p)
    (s : ℕ) (hst : s ≤ t) (j : Fin t) (x : Fin p)
    (hx : x ∈ tieSelection h t ht s j) :
    ∃ k : Fin (h + s), cyclicColumnIndex h t ht s hst j k = x := by
  classical
  rcases Finset.mem_union.mp hx with hp | hw
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨⟨a.val, by omega⟩, ?_⟩
    simp only [cyclicColumnIndex, dif_pos a.isLt]
    rfl
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
    have hbs : (b - j).val < s := (Finset.mem_filter.mp hb).2
    refine ⟨⟨h + (b - j).val, by omega⟩, ?_⟩
    have hn : ¬ h + (b - j).val < h := by omega
    simp only [cyclicColumnIndex, dif_neg hn, Nat.add_sub_cancel_left]
    congr 1
    change j + (b - j) = b
    abel

def cyclicFrame {m l h t : ℕ} [NeZero t]
    (U : Matrix (Fin m) (Fin m) ℝ) (ht : h + t ≤ min m l)
    (s : ℕ) (hst : s ≤ t) (j : Fin t) : Matrix (Fin m) (Fin (h + s)) ℝ :=
  U.submatrix id (fun k => Fin.castLE (Nat.min_le_left m l)
    (cyclicColumnIndex h t ht s hst j k))

theorem cyclicFrame_orthonormal {m l h t : ℕ} [NeZero t]
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (ht : h + t ≤ min m l) (s : ℕ) (hst : s ≤ t) (j : Fin t) :
    OrthonormalColumns (cyclicFrame U ht s hst j) := by
  apply orthonormalColumns_submatrix hU
  intro a b he
  apply cyclicColumnIndex_injective ht s hst j
  have hv : (cyclicColumnIndex h t ht s hst j a).val =
      (cyclicColumnIndex h t ht s hst j b).val := congrArg (fun x : Fin m => x.val) he
  exact Fin.ext hv

theorem cyclicFrame_space {m l h t : ℕ} [NeZero t]
    (U : Matrix (Fin m) (Fin m) ℝ) (ht : h + t ≤ min m l)
    (s : ℕ) (hst : s ≤ t) (j : Fin t) :
    frameSpace (cyclicFrame U ht s hst j) =
      directionSubspace U (tieSelection h t ht s j) := by
  classical
  unfold frameSpace directionSubspace singularSubspace
  congr 1
  ext v
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨cyclicColumnIndex h t ht s hst j k, cyclicColumnIndex_mem ht s hst j k⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨a, ha⟩ := cyclicColumnIndex_surjective ht s hst j k.val k.property
    refine ⟨a, ?_⟩
    change matrixColumn U (Fin.castLE (Nat.min_le_left m l)
      (cyclicColumnIndex h t ht s hst j a)) = _
    rw [ha]

theorem cyclicFrame_rank {m l h t : ℕ} [NeZero t]
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (ht : h + t ≤ min m l) (s : ℕ) (hst : s ≤ t) (j : Fin t) :
    Matrix.rank (cyclicFrame U ht s hst j) = h + s := by
  simpa only [Fintype.card_fin] using
    orthonormalColumns_rank (cyclicFrame_orthonormal hU ht s hst j)

theorem cyclicFrame_projection {m l h t : ℕ} [NeZero t]
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (ht : h + t ≤ min m l) (s : ℕ) (hst : s ≤ t) (j : Fin t)
    (B : Matrix (Fin m) (Fin l) ℝ) :
    cyclicFrame U ht s hst j * ((cyclicFrame U ht s hst j).transpose * B) =
      projectMatrix (directionSubspace U (tieSelection h t ht s j)) B := by
  rw [← frame_projectMatrix (cyclicFrame_orthonormal hU ht s hst j) B,
    cyclicFrame_space]

#assert_trust kernel cyclicColumnIndex_val
#assert_trust kernel cyclicColumnIndex_injective
#assert_trust kernel cyclicColumnIndex_mem
#assert_trust kernel cyclicColumnIndex_surjective
#assert_trust kernel cyclicFrame_orthonormal
#assert_trust kernel cyclicFrame_space
#assert_trust kernel cyclicFrame_rank
#assert_trust kernel cyclicFrame_projection
#print axioms cyclicFrame_projection
end NLA.Proofs.TR04.SVD
