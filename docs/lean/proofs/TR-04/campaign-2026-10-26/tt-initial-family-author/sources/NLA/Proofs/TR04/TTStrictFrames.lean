import NLA.Proofs.TR04.TTStrictBasics

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04.TensorFormat.TTStrict
open NLA.Computation.SVDMachine

/-- A finite family of actual first-mode matrices. Approximation properties
are proved separately; none is assumed by this data structure. -/
structure FirstFrames (m r : ℕ) where
  count : ℕ
  count_pos : 0 < count
  width : ℕ
  width_le : width ≤ r
  frame : Fin count → Matrix (Fin m) (Fin width) ℝ
  orthonormal : ∀ j, SVD.OrthonormalColumns (frame j)

instance {m r : ℕ} (F : FirstFrames m r) : NeZero F.count := ⟨Nat.ne_of_gt F.count_pos⟩

def defaultFrames {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V) (r : ℕ) : FirstFrames m r where
  count := 1
  count_pos := by decide
  width := cappedRank m l r
  width_le := Nat.min_le_left _ _
  frame := fun _ => prefixFrame (l := l) U r
  orthonormal := fun _ => prefixFrame_orthonormal h r

theorem defaultFrames_first_error {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V) (r : ℕ)
    (j : Fin (defaultFrames h r).count) :
    SVD.matrixEnergy (B - (defaultFrames h r).frame j *
      (((defaultFrames h r).frame j).transpose * B)) = SVD.tailEnergy sigma r := by
  rw [show (defaultFrames h r).frame j * (((defaultFrames h r).frame j).transpose * B) =
    SVD.truncate U sigma V r from SVD.validSVD_prefix_projection h r]
  exact SVD.validSVD_truncate_error h r

/-- The family depends only on the supplied first SVD and rank allowance.
It is selected before a comparator or any child completion responses. -/
theorem exists_firstFrames {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V) (r : ℕ) (hr : 1 ≤ r) :
    ∃ F : FirstFrames m r, F.count ≤ min m l + 1 ∧ F.width ≤ min m l ∧
      (∀ j, SVD.matrixEnergy (B - F.frame j * ((F.frame j).transpose * B)) =
        SVD.tailEnergy sigma r) ∧
      ∀ Y : Matrix (Fin m) (Fin l) ℝ, Matrix.rank Y ≤ r →
        SVD.matrixEnergy (B - Y) = SVD.tailEnergy sigma r →
        0 < SVD.matrixEnergy (B - Y) →
        ∃ j, SVD.matrixEnergy (F.frame j * ((F.frame j).transpose * (B - Y))) <
          SVD.matrixEnergy (B - Y) := by
  classical
  have fallback (hz : SVD.tailEnergy sigma r = 0) :
      ∃ F : FirstFrames m r, F.count ≤ min m l + 1 ∧ F.width ≤ min m l ∧
        (∀ j, SVD.matrixEnergy (B - F.frame j * ((F.frame j).transpose * B)) =
          SVD.tailEnergy sigma r) ∧
        ∀ Y : Matrix (Fin m) (Fin l) ℝ, Matrix.rank Y ≤ r →
          SVD.matrixEnergy (B - Y) = SVD.tailEnergy sigma r →
          0 < SVD.matrixEnergy (B - Y) →
          ∃ j, SVD.matrixEnergy (F.frame j * ((F.frame j).transpose * (B - Y))) <
            SVD.matrixEnergy (B - Y) := by
    refine ⟨defaultFrames h r, by simp [defaultFrames], Nat.min_le_right _ _,
      defaultFrames_first_error h r, ?_⟩
    intro Y _ he hp
    rw [hz] at he
    rw [he] at hp
    exact False.elim ((lt_irrefl 0) hp)
  by_cases hrp : r ≤ min m l
  · let a : Fin (min m l) := ⟨r - 1, by omega⟩
    have har : a.val + 1 = r := by dsimp [a]; omega
    by_cases ha : 0 < sigma a
    · obtain ⟨T⟩ := SVD.exists_tieStructure sigma h.2.2.2.1 a
      choose Q hQ hproj using fun j : Fin T.tied => T.exists_frame h.1 j
      let F : FirstFrames m r :=
        { count := T.tied
          count_pos := T.tied_pos
          width := a.val + 1
          width_le := har.le
          frame := Q
          orthonormal := hQ }
      refine ⟨F, ?_, ?_, ?_, ?_⟩
      · have hf := T.fits
        change T.tied ≤ min m l + 1
        omega
      · change a.val + 1 ≤ min m l
        omega
      · intro j
        change SVD.matrixEnergy (B - Q j * ((Q j).transpose * B)) = _
        rw [hproj j B]
        simpa only [har] using T.first_error h j
      · intro Y hY he hp
        obtain ⟨j, hj⟩ := T.equality_exists_strict_residual h ha Y (by simpa only [har] using hY)
          (by simpa only [har] using he) hp
        refine ⟨j, ?_⟩
        change SVD.matrixEnergy (Q j * ((Q j).transpose * (B - Y))) < _
        rw [hproj j (B - Y)]
        exact hj
    · apply fallback
      apply (SVD.tailEnergy_eq_zero_iff sigma r).mpr
      intro k hk
      have hs : sigma a = 0 := le_antisymm (le_of_not_gt ha) (h.2.2.1 a)
      have hle := h.2.2.2.1 a k (Fin.le_iff_val_le_val.mpr (by dsimp [a]; omega))
      rw [hs] at hle
      exact le_antisymm hle (h.2.2.1 k)
  · exact fallback (SVD.tailEnergy_eq_zero_of_length_le sigma (Nat.le_of_lt (Nat.lt_of_not_ge hrp)))

#assert_trust kernel exists_firstFrames
#print axioms exists_firstFrames
end NLA.Proofs.TR04.TensorFormat.TTStrict
