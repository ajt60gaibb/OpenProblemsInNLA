import NLA.Proofs.TR04.SVDExplicitCyclic

/-! The complete threshold block is determined by two finite comparison counts.
Its frames use the explicit prefix and cyclic column map. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04.SVD

def countedTieStructure {p : ℕ} (sigma : Fin p → ℝ) (hord : Antitone sigma)
    (a : Fin p) : TieStructure sigma a := by
  classical
  let H := Finset.univ.filter (fun k : Fin p => sigma a < sigma k)
  let G := Finset.univ.filter (fun k : Fin p => sigma a ≤ sigma k)
  let h := H.card
  let b := G.card
  have hH (k : Fin p) : sigma a < sigma k ↔ k.val < h := by
    exact lower_predicate_iff_lt_card (fun i => sigma a < sigma i)
      (fun i j hij hj => lt_of_lt_of_le hj (hord hij)) k
  have hG (k : Fin p) : sigma a ≤ sigma k ↔ k.val < b := by
    exact lower_predicate_iff_lt_card (fun i => sigma a ≤ sigma i)
      (fun i j hij hj => hj.trans (hord hij)) k
  have hhb : h ≤ b := Finset.card_le_card (by
    intro k hk
    simp only [H, G, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.le)
  have hha : h ≤ a.val := by
    have hn : ¬ sigma a < sigma a := lt_irrefl _
    rw [hH] at hn
    omega
  have hab : a.val < b := (hG a).mp le_rfl
  have hbp : b ≤ p := by
    have hc := Finset.card_le_card (Finset.filter_subset (fun k : Fin p => sigma a ≤ sigma k) Finset.univ)
    simpa only [Finset.card_univ, Fintype.card_fin] using hc
  refine {
    above := h
    tied := b - h
    take := a.val + 1 - h
    fits := by omega
    take_pos := by omega
    take_le := by omega
    rank_eq := by omega
    above_iff := hH
    equal_iff := ?_ }
  intro k
  have heq : h + (b - h) = b := by omega
  rw [heq]
  constructor
  · intro hk
    have hkG : k.val < b := (hG k).mp (by rw [hk])
    have hkH : ¬ k.val < h := by
      intro hh
      have := (hH k).mpr hh
      rw [hk] at this
      exact (lt_irrefl _) this
    exact ⟨Nat.le_of_not_gt hkH, hkG⟩
  · rintro ⟨hkH, hkG⟩
    have hl : sigma a ≤ sigma k := (hG k).mpr hkG
    have hu : sigma k ≤ sigma a := by
      by_contra hn
      have := (hH k).mp (lt_of_not_ge hn)
      omega
    exact le_antisymm hu hl


theorem countedTieStructure_above {p : ℕ} (sigma : Fin p → ℝ)
    (hord : Antitone sigma) (a : Fin p) :
    (countedTieStructure sigma hord a).above =
      (Finset.univ.filter (fun k => sigma a < sigma k)).card := rfl

theorem countedTieStructure_tied {p : ℕ} (sigma : Fin p → ℝ)
    (hord : Antitone sigma) (a : Fin p) :
    (countedTieStructure sigma hord a).tied =
      (Finset.univ.filter (fun k => sigma a ≤ sigma k)).card -
        (Finset.univ.filter (fun k => sigma a < sigma k)).card := rfl

theorem countedTieStructure_take {p : ℕ} (sigma : Fin p → ℝ)
    (hord : Antitone sigma) (a : Fin p) :
    (countedTieStructure sigma hord a).take = a.val + 1 -
      (Finset.univ.filter (fun k => sigma a < sigma k)).card := rfl

def TieStructure.explicitIndex {p : ℕ} {sigma : Fin p → ℝ} {a : Fin p}
    (T : TieStructure sigma a) (j : Fin T.tied) (k : Fin (a.val + 1)) : Fin p :=
  cyclicColumnIndex T.above T.tied T.fits T.take T.take_le j (Fin.cast T.rank_eq.symm k)

theorem TieStructure.explicitIndex_val {p : ℕ} {sigma : Fin p → ℝ} {a : Fin p}
    (T : TieStructure sigma a) (j : Fin T.tied) (k : Fin (a.val + 1)) :
    (T.explicitIndex j k).val = if k.val < T.above then k.val
      else T.above + ((j.val + (k.val - T.above)) % T.tied) :=
  cyclicColumnIndex_val T.fits T.take T.take_le j (Fin.cast T.rank_eq.symm k)

theorem TieStructure.explicitIndex_injective {p : ℕ} {sigma : Fin p → ℝ} {a : Fin p}
    (T : TieStructure sigma a) (j : Fin T.tied) : Function.Injective (T.explicitIndex j) := by
  intro x y he
  have hi := cyclicColumnIndex_injective T.fits T.take T.take_le j he
  apply Fin.ext
  exact congrArg (fun k : Fin (T.above + T.take) => k.val) hi

theorem TieStructure.explicitIndex_mem {p : ℕ} {sigma : Fin p → ℝ} {a : Fin p}
    (T : TieStructure sigma a) (j : Fin T.tied) (k : Fin (a.val + 1)) :
    T.explicitIndex j k ∈ tieSelection T.above T.tied T.fits T.take j :=
  cyclicColumnIndex_mem T.fits T.take T.take_le j (Fin.cast T.rank_eq.symm k)

theorem TieStructure.explicitIndex_surjective {p : ℕ} {sigma : Fin p → ℝ} {a : Fin p}
    (T : TieStructure sigma a) (j : Fin T.tied) (x : Fin p)
    (hx : x ∈ tieSelection T.above T.tied T.fits T.take j) :
    ∃ k : Fin (a.val + 1), T.explicitIndex j k = x := by
  obtain ⟨k, hk⟩ := cyclicColumnIndex_surjective T.fits T.take T.take_le j x hx
  refine ⟨Fin.cast T.rank_eq k, ?_⟩
  have he : Fin.cast T.rank_eq.symm (Fin.cast T.rank_eq k) = k := Fin.ext rfl
  rw [TieStructure.explicitIndex, he]
  exact hk

def TieStructure.explicitFrame {m l : ℕ} {sigma : Fin (min m l) → ℝ}
    {a : Fin (min m l)} (T : TieStructure sigma a)
    (U : Matrix (Fin m) (Fin m) ℝ) (j : Fin T.tied) :
    Matrix (Fin m) (Fin (a.val + 1)) ℝ :=
  U.submatrix id (fun k => Fin.castLE (Nat.min_le_left m l) (T.explicitIndex j k))

theorem TieStructure.explicitFrame_orthonormal {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)} (T : TieStructure sigma a)
    (j : Fin T.tied) : OrthonormalColumns (T.explicitFrame U j) := by
  apply orthonormalColumns_submatrix hU
  intro x y he
  apply T.explicitIndex_injective j
  apply Fin.ext
  exact congrArg (fun k : Fin m => k.val) he

theorem TieStructure.explicitFrame_space {m l : ℕ}
    (U : Matrix (Fin m) (Fin m) ℝ) {sigma : Fin (min m l) → ℝ}
    {a : Fin (min m l)} (T : TieStructure sigma a) (j : Fin T.tied) :
    frameSpace (T.explicitFrame U j) =
      directionSubspace U (tieSelection T.above T.tied T.fits T.take j) := by
  have hspace : frameSpace (T.explicitFrame U j) =
      frameSpace (cyclicFrame U T.fits T.take T.take_le j) := by
    unfold frameSpace
    congr 1
    let e : Fin (a.val + 1) ≃ Fin (T.above + T.take) := finCongr T.rank_eq.symm
    exact e.surjective.range_comp (fun k =>
      (WithLp.toLp 2 (fun i => cyclicFrame U T.fits T.take T.take_le j i k) : Space m))
  rw [hspace, cyclicFrame_space]

theorem TieStructure.explicitFrame_projection {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)} (T : TieStructure sigma a)
    (j : Fin T.tied) (B : Matrix (Fin m) (Fin l) ℝ) :
    T.explicitFrame U j * ((T.explicitFrame U j).transpose * B) =
      projectMatrix (directionSubspace U (tieSelection T.above T.tied T.fits T.take j)) B := by
  rw [← frame_projectMatrix (T.explicitFrame_orthonormal hU j) B, T.explicitFrame_space]

theorem TieStructure.explicitFrame_rank {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)} (T : TieStructure sigma a)
    (j : Fin T.tied) : Matrix.rank (T.explicitFrame U j) = a.val + 1 := by
  simpa only [Fintype.card_fin] using orthonormalColumns_rank (T.explicitFrame_orthonormal hU j)

#assert_trust kernel countedTieStructure
#assert_trust kernel countedTieStructure_above
#assert_trust kernel countedTieStructure_tied
#assert_trust kernel countedTieStructure_take
#assert_trust kernel TieStructure.explicitIndex_val
#assert_trust kernel TieStructure.explicitIndex_injective
#assert_trust kernel TieStructure.explicitIndex_mem
#assert_trust kernel TieStructure.explicitIndex_surjective
#assert_trust kernel TieStructure.explicitFrame_orthonormal
#assert_trust kernel TieStructure.explicitFrame_space
#assert_trust kernel TieStructure.explicitFrame_projection
#assert_trust kernel TieStructure.explicitFrame_rank
#print axioms TieStructure.explicitFrame_projection
end NLA.Proofs.TR04.SVD
