import NLA.Proofs.MF03.FiniteColumnCutPath

/-!
Exact intermediate-cut comparison for literal finite valid paths, and
cuts of the path reconstructed from a finite column system.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- At the top cut of a length-`N` path, no factor has yet been applied. -/
theorem finitePathAtCut_top (m N : ℕ) (X Z : StrictRows m)
    (c : FiniteValidPath m N X Z) :
    finitePathAtCut m N X Z c N = X := by
  cases N with
  | zero => rfl
  | succ n =>
      rcases c with ⟨Y, ⟨hstep, tail⟩⟩
      change (if n + 1 = n + 1 then X else
        finitePathAtCut m n Y Z tail (n + 1)) = X
      simp

/-- Equal tuples at every factor-label cut imply equality of the
entire literal valid chains. -/
theorem finiteValidPath_eq_of_cuts (m : ℕ) :
    ∀ (N : ℕ) (X Z : StrictRows m)
      (c c' : FiniteValidPath m N X Z),
      (∀ (q : ℕ), q ≤ N →
        finitePathAtCut m N X Z c q =
          finitePathAtCut m N X Z c' q) → c = c' := by
  intro N
  induction N with
  | zero =>
      intro X Z c c' _
      cases c
      cases c'
      rfl
  | succ n ih =>
      intro X Z c c' hcuts
      rcases c with ⟨Y, ⟨hstep, tail⟩⟩
      rcases c' with ⟨Y', ⟨hstep', tail'⟩⟩
      have hY : Y = Y' := by
        have hcut := hcuts n (by omega)
        change (if n = n + 1 then X else
            finitePathAtCut m n Y Z tail n) =
          (if n = n + 1 then X else
            finitePathAtCut m n Y' Z tail' n) at hcut
        simpa [finitePathAtCut_top, show n ≠ n + 1 by omega] using hcut
      subst Y'
      have htail : tail = tail' := by
        apply ih Y Z tail tail'
        intro q hq
        have hcut := hcuts q (by omega)
        change (if q = n + 1 then X else
            finitePathAtCut m n Y Z tail q) =
          (if q = n + 1 then X else
            finitePathAtCut m n Y Z tail' q) at hcut
        simpa [show q ≠ n + 1 by omega] using hcut
      subst tail'
      have hproof : hstep = hstep' := Subsingleton.elim _ _
      cases hproof
      rfl

/-- Every cut of the auxiliary chain assembled from column labels is
the explicitly reconstructed tuple at that cut. -/
theorem finiteColumnCutPathAux_atCut {N m j : ℕ} (hj : j ≤ m)
    (D : FiniteColumnSystem N m j) :
    ∀ (n : ℕ) (hn : n ≤ N) (q : ℕ) (hq : q ≤ n),
      finitePathAtCut m n
        (finiteColumnCutRows hj D n hn)
        (finiteColumnCutRows hj D 0 (Nat.zero_le N))
        (finiteColumnCutPathAux hj D n hn) q =
          finiteColumnCutRows hj D q (by omega) := by
  intro n
  induction n with
  | zero =>
      intro hn q hq
      have hq0 : q = 0 := by omega
      subst q
      rfl
  | succ n ih =>
      intro hn q hq
      by_cases htop : q = n + 1
      · subst q
        exact finitePathAtCut_top m (n + 1)
          (finiteColumnCutRows hj D (n + 1) hn)
          (finiteColumnCutRows hj D 0 (Nat.zero_le N))
          (finiteColumnCutPathAux hj D (n + 1) hn)
      · have hn' : n ≤ N := by omega
        have hq' : q ≤ n := by omega
        change (if q = n + 1 then
            finiteColumnCutRows hj D (n + 1) hn else
            finitePathAtCut m n
              (finiteColumnCutRows hj D n hn')
              (finiteColumnCutRows hj D 0 (Nat.zero_le N))
              (finiteColumnCutPathAux hj D n hn') q) =
              finiteColumnCutRows hj D q (by omega)
        simpa [htop] using ih hn' q hq'

#assert_trust kernel finiteValidPath_eq_of_cuts
#assert_trust kernel finiteColumnCutPathAux_atCut
#print axioms finiteValidPath_eq_of_cuts

end NLA.Proofs.MF03
