import NLA.Proofs.MF03.FiniteUniformTableau

/-!
Read an exact finite augmented tableau as equal-length columns. The only
extra value is the temporary sentinel at the bottom of each short column.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- An upper rectangular cell of the original augmented shape. -/
theorem finiteTableau_rect_cell (m j : ℕ)
    (r c : ℕ) (hr : r < m) (hc : c < m) :
    (r, c) ∈ finiteAugShape m j :=
  (mem_finiteAugShape m j r c).mpr (Or.inl ⟨hr, hc⟩)

/-- A bottom cell exists exactly in a long column. -/
theorem finiteTableau_bottom_cell (m j : ℕ) (hj : j ≤ m)
    (c : ℕ) (hc : c < j) :
    (m, c) ∈ finiteAugShape m j := by
  apply (mem_finiteAugShape m j m c).mpr
  exact Or.inr ⟨rfl, by simpa [min_eq_left hj] using hc⟩

/-- Uniform column values of a tableau: actual entries at original cells,
and `N` only at the omitted bottom cell of a short column. -/
def finiteTableauUniformValue {N m j : ℕ}
    (T : FiniteTableau (finiteAugShape m j) N)
    (p : Fin m) (r : Fin (m + 1)) : ℕ :=
  if r.val < m then T.1 r.val p.val
  else if p.val < j then T.1 m p.val else N

/-- Every uniform tableau column is strictly increasing. -/
theorem finiteTableauUniformValue_strictMono {N m j : ℕ}
    (hj : j ≤ m) (T : FiniteTableau (finiteAugShape m j) N)
    (p : Fin m) :
    StrictMono (finiteTableauUniformValue T p) := by
  intro r s hrs
  have hrs' : r.val < s.val := Fin.lt_def.mp hrs
  have hslim : s.val ≤ m := by have := s.isLt; omega
  by_cases hsm : s.val < m
  · have hrm : r.val < m := by omega
    have hcell := finiteTableau_rect_cell m j s.val p.val hsm p.isLt
    have hstrict := T.1.col_strict hrs' hcell
    simpa [finiteTableauUniformValue, hrm, hsm] using hstrict
  · have hseq : s.val = m := by omega
    have hrm : r.val < m := by omega
    by_cases hp : p.val < j
    · have hcell := finiteTableau_bottom_cell m j hj p.val hp
      have hstrict := T.1.col_strict (by omega : r.val < m) hcell
      simpa [finiteTableauUniformValue, hrm, hsm, hp, hseq]
        using hstrict
    · have hcell := finiteTableau_rect_cell m j r.val p.val hrm p.isLt
      have hbound := T.2 r.val p.val hcell
      simpa [finiteTableauUniformValue, hrm, hsm, hp] using hbound

/-- At every uniform row, the tableau values are weakly increasing from
left to right, including the temporary bottom sentinels. -/
theorem finiteTableauUniformValue_row_monotone {N m j : ℕ}
    (hj : j ≤ m) (T : FiniteTableau (finiteAugShape m j) N)
    (r : Fin (m + 1)) :
    Monotone (fun p : Fin m => finiteTableauUniformValue T p r) := by
  intro p q hpq
  have hpq' : p.val ≤ q.val := Fin.le_def.mp hpq
  by_cases hrm : r.val < m
  · by_cases heq : p = q
    · subst q
      exact le_rfl
    · have hlt : p.val < q.val := by
        have hne : p.val ≠ q.val := by
          intro h
          exact heq (Fin.ext h)
        omega
      have hcell := finiteTableau_rect_cell m j r.val q.val hrm q.isLt
      have hrow := T.1.row_weak hlt hcell
      simpa [finiteTableauUniformValue, hrm] using hrow
  · have hreq : r.val = m := by have := r.isLt; omega
    by_cases hq : q.val < j
    · have hp : p.val < j := by omega
      by_cases heq : p = q
      · subst q
        exact le_rfl
      · have hlt : p.val < q.val := by
          have hne : p.val ≠ q.val := by
            intro h
            exact heq (Fin.ext h)
          omega
        have hcell := finiteTableau_bottom_cell m j hj q.val hq
        have hrow := T.1.row_weak hlt hcell
        simpa [finiteTableauUniformValue, hrm, hp, hq] using hrow
    · by_cases hp : p.val < j
      · have hcell := finiteTableau_bottom_cell m j hj p.val hp
        have hbound := T.2 m p.val hcell
        simpa [finiteTableauUniformValue, hrm, hp, hq] using hbound.le
      · simp [finiteTableauUniformValue, hrm, hp, hq]

#assert_trust kernel finiteTableauUniformValue_strictMono
#assert_trust kernel finiteTableauUniformValue_row_monotone
#print axioms finiteTableauUniformValue_row_monotone

end NLA.Proofs.MF03
