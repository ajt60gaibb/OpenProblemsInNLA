import NLA.Proofs.TR04.TTStrictFamily
import NLA.Proofs.TR04.SVDExplicitTie

/-! Deterministic finite first-frame family. Its data use only comparisons of
the supplied singular values, finite comparison counts, and explicit columns. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04.TensorFormat.TTStrict
open NLA.Computation.SVDMachine

def positiveFrames {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (r : ℕ) (hr : 1 ≤ r) (hrp : r ≤ min m l) : FirstFrames m r :=
  let a : Fin (min m l) := ⟨r - 1, by omega⟩
  let T := SVD.countedTieStructure sigma h.2.2.2.1 a
  { count := T.tied
    count_pos := T.tied_pos
    width := a.val + 1
    width_le := by dsimp [a]; omega
    frame := T.explicitFrame U
    orthonormal := T.explicitFrame_orthonormal h.1 }

def explicitFirstFrames {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V) (r : ℕ) : FirstFrames m r :=
  if hr : 1 ≤ r then
    if hrp : r ≤ min m l then
      if 0 < sigma ⟨r - 1, by omega⟩ then positiveFrames h r hr hrp
      else defaultFrames h r
    else defaultFrames h r
  else defaultFrames h r

theorem explicitFirstFrames_eq_positive {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (r : ℕ) (hr : 1 ≤ r) (hrp : r ≤ min m l)
    (ha : 0 < sigma ⟨r - 1, by omega⟩) :
    explicitFirstFrames h r = positiveFrames h r hr hrp := by
  rw [explicitFirstFrames, dif_pos hr, dif_pos hrp, if_pos ha]

theorem explicitFirstFrames_eq_default_large {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (r : ℕ) (hrp : ¬ r ≤ min m l) : explicitFirstFrames h r = defaultFrames h r := by
  unfold explicitFirstFrames
  by_cases hr : 1 ≤ r
  · rw [dif_pos hr, dif_neg hrp]
  · rw [dif_neg hr]

theorem explicitFirstFrames_eq_default_nonpos {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (r : ℕ) (hr : 1 ≤ r) (hrp : r ≤ min m l)
    (ha : sigma ⟨r - 1, by omega⟩ ≤ 0) : explicitFirstFrames h r = defaultFrames h r := by
  rw [explicitFirstFrames, dif_pos hr, dif_pos hrp, if_neg (not_lt_of_ge ha)]

theorem positiveFrames_width {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (r : ℕ) (hr : 1 ≤ r) (hrp : r ≤ min m l) : (positiveFrames h r hr hrp).width = r := by
  change r - 1 + 1 = r
  omega

theorem positiveFrames_column {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (r : ℕ) (hr : 1 ≤ r) (hrp : r ≤ min m l)
    (j : Fin (positiveFrames h r hr hrp).count) (i : Fin m)
    (k : Fin (positiveFrames h r hr hrp).width) :
    let a : Fin (min m l) := ⟨r - 1, by omega⟩
    let T := SVD.countedTieStructure sigma h.2.2.2.1 a
    (positiveFrames h r hr hrp).frame j i k =
      U i (Fin.castLE (Nat.min_le_left m l) (T.explicitIndex j k)) := rfl

theorem positiveFrames_count {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (r : ℕ) (hr : 1 ≤ r) (hrp : r ≤ min m l) :
    let a : Fin (min m l) := ⟨r - 1, by omega⟩
    (positiveFrames h r hr hrp).count =
      (Finset.univ.filter (fun k => sigma a ≤ sigma k)).card -
        (Finset.univ.filter (fun k => sigma a < sigma k)).card := rfl

/-- The explicit family has the same universal first error and strict equality
gate, with no comparator or child-response input to its selection. -/
theorem explicitFirstFrames_spec {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V) (r : ℕ) (hr : 1 ≤ r) :
    let F := explicitFirstFrames h r
    F.count ≤ min m l + 1 ∧ F.width ≤ min m l ∧
      (∀ j, SVD.matrixEnergy (B - F.frame j * ((F.frame j).transpose * B)) =
        SVD.tailEnergy sigma r) ∧
      ∀ Y : Matrix (Fin m) (Fin l) ℝ, Matrix.rank Y ≤ r →
        SVD.matrixEnergy (B - Y) = SVD.tailEnergy sigma r →
        0 < SVD.matrixEnergy (B - Y) →
        ∃ j, SVD.matrixEnergy (F.frame j * ((F.frame j).transpose * (B - Y))) <
          SVD.matrixEnergy (B - Y) := by
  classical
  have fallback (hz : SVD.tailEnergy sigma r = 0) :
      (defaultFrames h r).count ≤ min m l + 1 ∧ (defaultFrames h r).width ≤ min m l ∧
      (∀ j, SVD.matrixEnergy (B - (defaultFrames h r).frame j *
        (((defaultFrames h r).frame j).transpose * B)) = SVD.tailEnergy sigma r) ∧
      ∀ Y : Matrix (Fin m) (Fin l) ℝ, Matrix.rank Y ≤ r →
        SVD.matrixEnergy (B - Y) = SVD.tailEnergy sigma r →
        0 < SVD.matrixEnergy (B - Y) →
        ∃ j, SVD.matrixEnergy ((defaultFrames h r).frame j *
          (((defaultFrames h r).frame j).transpose * (B - Y))) < SVD.matrixEnergy (B - Y) := by
    refine ⟨by simp [defaultFrames], Nat.min_le_right _ _, defaultFrames_first_error h r, ?_⟩
    intro Y _ he hp
    rw [hz] at he
    rw [he] at hp
    exact False.elim ((lt_irrefl 0) hp)
  dsimp only
  rw [explicitFirstFrames, dif_pos hr]
  by_cases hrp : r ≤ min m l
  · rw [dif_pos hrp]
    let a : Fin (min m l) := ⟨r - 1, by omega⟩
    have har : a.val + 1 = r := by dsimp [a]; omega
    by_cases ha : 0 < sigma a
    · rw [if_pos ha]
      let T := SVD.countedTieStructure sigma h.2.2.2.1 a
      change T.tied ≤ min m l + 1 ∧ a.val + 1 ≤ min m l ∧ _
      refine ⟨by have hf := T.fits; omega, by omega, ?_, ?_⟩
      · intro j
        change SVD.matrixEnergy (B - T.explicitFrame U j * ((T.explicitFrame U j).transpose * B)) = _
        rw [T.explicitFrame_projection h.1 j B]
        simpa only [har] using T.first_error h j
      · intro Y hY he hp
        obtain ⟨j, hj⟩ := T.equality_exists_strict_residual h ha Y
          (by simpa only [har] using hY) (by simpa only [har] using he) hp
        refine ⟨j, ?_⟩
        change SVD.matrixEnergy (T.explicitFrame U j * ((T.explicitFrame U j).transpose * (B - Y))) < _
        rw [T.explicitFrame_projection h.1 j (B - Y)]
        exact hj
    · rw [if_neg ha]
      apply fallback
      apply (SVD.tailEnergy_eq_zero_iff sigma r).mpr
      intro k hk
      have hs : sigma a = 0 := le_antisymm (le_of_not_gt ha) (h.2.2.1 a)
      have hle := h.2.2.2.1 a k (Fin.le_iff_val_le_val.mpr (by dsimp [a]; omega))
      rw [hs] at hle
      exact le_antisymm hle (h.2.2.1 k)
  · rw [dif_neg hrp]
    exact fallback (SVD.tailEnergy_eq_zero_of_length_le sigma (Nat.le_of_lt (Nat.lt_of_not_ge hrp)))

#assert_trust kernel positiveFrames
#assert_trust kernel explicitFirstFrames
#assert_trust kernel explicitFirstFrames_eq_positive
#assert_trust kernel explicitFirstFrames_eq_default_large
#assert_trust kernel explicitFirstFrames_eq_default_nonpos
#assert_trust kernel positiveFrames_width
#assert_trust kernel positiveFrames_column
#assert_trust kernel positiveFrames_count
#assert_trust kernel explicitFirstFrames_spec
#print axioms explicitFirstFrames_spec
end NLA.Proofs.TR04.TensorFormat.TTStrict
