import NLA.Proofs.TR14.ChartUpperConstruction
import NLA.Proofs.TR14.NormalizedOrdinaryLower
import NLA.Proofs.TR14.WidthPadding
import NLA.Proofs.TR14.WidthBasics

/-! The unchanged full all-width TR-14 target. For nonzero data, both actual
symmetric constructions and the unrestricted ordinary lower bound use the
same chosen normalized least-apolar chart. Actual width transport and zero
padding return the requested width in the original coordinates. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open NLA.Statements.TR14

/-- Every ordinary width of every complex Hankel tensor is a symmetric width,
with the original data, all exceptional cases and empty decompositions. -/
theorem ordinaryWidth_to_symmetricWidth {m n w : ℕ} (hm : 3 ≤ m) (hn : 2 ≤ n)
    (h : Fin (m * (n - 1) + 1) → ℂ) (hw : OrdinaryWidth (Hankel h) w) :
    SymmetricWidth (Hankel h) w := by
  by_cases hh : h = 0
  · subst h
    apply symmetricWidth_mono (Nat.zero_le w)
    apply (symmetricWidth_zero_iff _).mpr
    intro i
    rfl
  · cases n with
    | zero => omega
    | succ q =>
        obtain ⟨z, g, hrD, hg, hrLo, hrHi, htrans, hAp, hmin, hbin, hlocal⟩ :=
          exists_chart_two_symmetricWidths hm hn h hh
        have hord := chart_ordinaryWidth_forward z m q w h hw
        have hbound := ordinary_lower_of_minimal_monic_succ hm (by omega)
          (transformedMoments z h) htrans g hg hrLo hrD hrHi hAp hmin hord
        have hsym : SymmetricWidth (Hankel h)
            (min (m * q - g.natDegree + 2)
              ((m - 1) * g.natDegree - (m - 2) * (localRootSupport g).card)) := by
          rcases le_total (m * q - g.natDegree + 2)
              ((m - 1) * g.natDegree - (m - 2) * (localRootSupport g).card) with hab | hba
          · rw [min_eq_left hab]
            exact hbin
          · rw [min_eq_right hba]
            exact hlocal
        exact symmetricWidth_mono hbound hsym

/-- Complete original TR-14 target, without additional mathematical premises. -/
theorem target : NLA.Statements.TR14.Target := by
  intro m n hm hn h w
  exact ⟨ordinaryWidth_to_symmetricWidth hm hn h,
    symmetricWidth_to_ordinaryWidth (by omega)⟩

#assert_trust kernel ordinaryWidth_to_symmetricWidth
#assert_trust kernel target
#print axioms target

end NLA.Proofs.TR14
