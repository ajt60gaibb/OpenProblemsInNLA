import NLA.Proofs.MF03.FiniteLabelSuffixStep

/-!
At cut `q`, place path `p` at its original starting position plus the
number of its actual labels at or above `q`. The source-locked one-gap
noncollision condition makes this an ordered tuple at every cut.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- Natural-valued position of path `p` at factor-label cut `q`. -/
def finiteColumnCutNat {N m j : ℕ} (hj : j ≤ m)
    (D : FiniteColumnSystem N m j) (q : ℕ) (p : Fin m) : ℕ :=
  ((finitePathStart m j hj).1 p).val +
    finiteLabelSuffix (D.labels p) q

theorem finiteColumn_start_le_end (m j : ℕ) (hj : j ≤ m)
    (p : Fin m) :
    ((finitePathStart m j hj).1 p).val ≤
      ((finitePathEnd m).1 p).val := by
  change (if p.val < j then p.val else p.val + 1) ≤ m + 1 + p.val
  split_ifs <;> omega

/-- Every cut position remains inside the original `Fin (2m+1)` sites. -/
theorem finiteColumnCutNat_bound {N m j : ℕ} (hj : j ≤ m)
    (D : FiniteColumnSystem N m j) (q : ℕ) (p : Fin m) :
    finiteColumnCutNat hj D q p < 2 * m + 1 := by
  have hsub : finiteLabelSuffix (D.labels p) q ≤ (D.labels p).card :=
    Finset.card_filter_le (D.labels p) (fun k => q ≤ k)
  have hcard := D.card_eq p
  have hdisp := finitePath_advance_count m j hj p
  have hstart := finiteColumn_start_le_end m j hj p
  have hend := ((finitePathEnd m).1 p).isLt
  unfold finiteColumnCutNat
  omega

/-- Adjacent cut positions are strictly ordered with exactly the
original omitted-row allowance at `p+1=j`. -/
theorem finiteColumnCutNat_adjacent {N m j : ℕ} (hj : j ≤ m)
    (D : FiniteColumnSystem N m j) (q : ℕ) (hq : q ≤ N)
    (p : Fin m) (hp : p.val + 1 < m) :
    finiteColumnCutNat hj D q p <
      finiteColumnCutNat hj D q ⟨p.val + 1, hp⟩ := by
  let p' : Fin m := ⟨p.val + 1, hp⟩
  have hnc := D.noncollision q hq p hp
  change finiteLabelSuffix (D.labels p) q ≤
    finiteLabelSuffix (D.labels p') q +
      (if p.val + 1 = j then 1 else 0) at hnc
  have hgap :
      ((finitePathStart m j hj).1 p').val =
        ((finitePathStart m j hj).1 p).val +
          (if p.val + 1 = j then 2 else 1) := by
    change (if p.val + 1 < j then p.val + 1 else p.val + 2) =
      (if p.val < j then p.val else p.val + 1) +
        (if p.val + 1 = j then 2 else 1)
    split_ifs <;> omega
  change ((finitePathStart m j hj).1 p).val +
      finiteLabelSuffix (D.labels p) q <
    ((finitePathStart m j hj).1 p').val +
      finiteLabelSuffix (D.labels p') q
  rw [hgap]
  split_ifs at hnc ⊢ <;> omega

/-- All cut positions are strictly ordered, beyond adjacent columns. -/
theorem finiteColumnCutNat_strictMono {N m j : ℕ} (hj : j ≤ m)
    (D : FiniteColumnSystem N m j) (q : ℕ) (hq : q ≤ N) :
    StrictMono (finiteColumnCutNat hj D q) := by
  cases m with
  | zero =>
      intro p _ _
      exact Fin.elim0 p
  | succ n =>
      apply Fin.strictMono_iff_lt_succ.mpr
      intro p
      exact finiteColumnCutNat_adjacent hj D q hq p.castSucc
        (by
          change p.val + 1 < n + 1
          omega)

/-- The literal ordered tuple at a factor-label cut. -/
def finiteColumnCutRows {N m j : ℕ} (hj : j ≤ m)
    (D : FiniteColumnSystem N m j) (q : ℕ) (hq : q ≤ N) :
    StrictRows m :=
  ⟨fun p => ⟨finiteColumnCutNat hj D q p,
      finiteColumnCutNat_bound hj D q p⟩,
    by
      intro p p' hpp'
      exact Fin.lt_def.mpr
        (finiteColumnCutNat_strictMono hj D q hq hpp')⟩

#assert_trust kernel finiteColumnCutRows
#print axioms finiteColumnCutRows

end NLA.Proofs.MF03
