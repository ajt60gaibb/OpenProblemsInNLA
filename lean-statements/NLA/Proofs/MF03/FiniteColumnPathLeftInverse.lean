import NLA.Proofs.MF03.FiniteColumnCutPath

/-!
The path reconstructed from an exact finite column system advances at
precisely its original labels. This proves the first literal inverse,
without enumerating any path order or changing the tableau domain.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

private theorem finiteColumnSystem_eq_of_labels {N m j : ℕ}
    (A B : FiniteColumnSystem N m j) (h : A.labels = B.labels) :
    A = B := by
  cases A with
  | mk a ah ac an =>
    cases B with
    | mk b bh bc bn =>
      dsimp at h
      subst b
      rfl

private theorem finiteAdvanceLabels_castTypes {m N : ℕ}
    {X X' Z Z' : StrictRows m} (hX : X = X') (hZ : Z = Z')
    (hType1 : FiniteValidPath m N X Z = FiniteValidPath m N X' Z)
    (hType2 : FiniteValidPath m N X' Z = FiniteValidPath m N X' Z')
    (c : FiniteValidPath m N X Z) (p : Fin m) :
    finiteAdvanceLabels m N X' Z' (Eq.mp hType2 (Eq.mp hType1 c)) p =
      finiteAdvanceLabels m N X Z c p := by
  cases hX
  cases hZ
  cases hType1
  cases hType2
  rfl

/-- The auxiliary chain through labels below `n` has exactly the original
column labels below `n`. -/
theorem finiteColumnCutPathAux_labels {N m j : ℕ} (hj : j ≤ m)
    (D : FiniteColumnSystem N m j) :
    ∀ (n : ℕ) (hn : n ≤ N) (p : Fin m),
      finiteAdvanceLabels m n
        (finiteColumnCutRows hj D n hn)
        (finiteColumnCutRows hj D 0 (Nat.zero_le N))
        (finiteColumnCutPathAux hj D n hn) p =
          (D.labels p).filter (fun k => k < n) := by
  intro n
  induction n with
  | zero =>
      intro hn p
      simp [finiteAdvanceLabels]
  | succ n ih =>
      intro hn p
      have hn' : n ≤ N := by omega
      have hstep := finiteLabelSuffix_step (D.labels p) n
      by_cases hmem : n ∈ D.labels p
      · have hmove :
            ((finiteColumnCutRows hj D n hn').1 p).val =
              ((finiteColumnCutRows hj D (n + 1) hn).1 p).val + 1 := by
          change finiteColumnCutNat hj D n p =
            finiteColumnCutNat hj D (n + 1) p + 1
          unfold finiteColumnCutNat
          simp only [if_pos hmem] at hstep
          omega
        have hfilter :
            (D.labels p).filter (fun k => k < n + 1) =
              insert n ((D.labels p).filter (fun k => k < n)) := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · intro hk
            by_cases hkn : k = n
            · exact Or.inl hkn
            · exact Or.inr ⟨hk.1, by omega⟩
          · intro hk
            rcases hk with rfl | hk
            · exact ⟨hmem, by omega⟩
            · exact ⟨hk.1, by omega⟩
        change (if ((finiteColumnCutRows hj D n hn').1 p).val =
            ((finiteColumnCutRows hj D (n + 1) hn).1 p).val + 1 then
          insert n (finiteAdvanceLabels m n
            (finiteColumnCutRows hj D n hn')
            (finiteColumnCutRows hj D 0 (Nat.zero_le N))
            (finiteColumnCutPathAux hj D n hn') p)
          else finiteAdvanceLabels m n
            (finiteColumnCutRows hj D n hn')
            (finiteColumnCutRows hj D 0 (Nat.zero_le N))
            (finiteColumnCutPathAux hj D n hn') p) =
              (D.labels p).filter (fun k => k < n + 1)
        rw [if_pos hmove, ih hn' p]
        exact hfilter.symm
      · have hstay :
            ((finiteColumnCutRows hj D n hn').1 p).val =
              ((finiteColumnCutRows hj D (n + 1) hn).1 p).val := by
          change finiteColumnCutNat hj D n p =
            finiteColumnCutNat hj D (n + 1) p
          unfold finiteColumnCutNat
          simp only [if_neg hmem] at hstep
          omega
        have hnotmove :
            ((finiteColumnCutRows hj D n hn').1 p).val ≠
              ((finiteColumnCutRows hj D (n + 1) hn).1 p).val + 1 := by
          omega
        have hfilter :
            (D.labels p).filter (fun k => k < n + 1) =
              (D.labels p).filter (fun k => k < n) := by
          ext k
          simp only [Finset.mem_filter]
          constructor
          · intro hk
            have hkn : k ≠ n := by
              intro heq
              subst k
              exact hmem hk.1
            exact ⟨hk.1, by omega⟩
          · intro hk
            exact ⟨hk.1, by omega⟩
        change (if ((finiteColumnCutRows hj D n hn').1 p).val =
            ((finiteColumnCutRows hj D (n + 1) hn).1 p).val + 1 then
          insert n (finiteAdvanceLabels m n
            (finiteColumnCutRows hj D n hn')
            (finiteColumnCutRows hj D 0 (Nat.zero_le N))
            (finiteColumnCutPathAux hj D n hn') p)
          else finiteAdvanceLabels m n
            (finiteColumnCutRows hj D n hn')
            (finiteColumnCutRows hj D 0 (Nat.zero_le N))
            (finiteColumnCutPathAux hj D n hn') p) =
              (D.labels p).filter (fun k => k < n + 1)
        rw [if_neg hnotmove, ih hn' p]
        exact hfilter.symm

/-- Extracting the advance-label column system from its reconstructed
valid path returns every original label set exactly. -/
theorem finiteColumnPath_leftInverse {N m j : ℕ} (hj : j ≤ m)
    (D : FiniteColumnSystem N m j) :
    finitePathToColumnSystem N m j hj
      (finiteColumnSystemToPath hj D) = D := by
  have hlabels :
      (finitePathToColumnSystem N m j hj
        (finiteColumnSystemToPath hj D)).labels = D.labels := by
    funext p
    change finiteAdvanceLabels m N
      (finitePathStart m j hj) (finitePathEnd m)
      (finiteColumnSystemToPath hj D) p = D.labels p
    have haux := finiteColumnCutPathAux_labels hj D N le_rfl p
    have htop := finiteColumnCutRows_top hj D
    have hzero := finiteColumnCutRows_zero hj D
    have hfilter : (D.labels p).filter (fun k => k < N) = D.labels p := by
      ext k
      simp only [Finset.mem_filter]
      constructor
      · exact And.left
      · intro hk
        exact ⟨hk, D.label_lt p k hk⟩
    let htype1 :
        FiniteValidPath m N
            (finiteColumnCutRows hj D N le_rfl)
            (finiteColumnCutRows hj D 0 (Nat.zero_le N)) =
          FiniteValidPath m N (finitePathStart m j hj)
            (finiteColumnCutRows hj D 0 (Nat.zero_le N)) :=
      congrArg (fun X => FiniteValidPath m N X
        (finiteColumnCutRows hj D 0 (Nat.zero_le N))) htop
    let htype2 :
        FiniteValidPath m N (finitePathStart m j hj)
            (finiteColumnCutRows hj D 0 (Nat.zero_le N)) =
          FiniteValidPath m N (finitePathStart m j hj) (finitePathEnd m) :=
      congrArg (fun Z => FiniteValidPath m N (finitePathStart m j hj) Z) hzero
    have hcast : finiteColumnSystemToPath hj D =
        Eq.mp htype2 (Eq.mp htype1
          (finiteColumnCutPathAux hj D N le_rfl)) := by
      rfl
    rw [hcast]
    exact (finiteAdvanceLabels_castTypes htop hzero htype1 htype2
      (finiteColumnCutPathAux hj D N le_rfl) p).trans
      (haux.trans hfilter)
  exact finiteColumnSystem_eq_of_labels _ _ hlabels

#assert_trust kernel finiteColumnCutPathAux_labels
#assert_trust kernel finiteColumnPath_leftInverse
#print axioms finiteColumnPath_leftInverse

end NLA.Proofs.MF03
