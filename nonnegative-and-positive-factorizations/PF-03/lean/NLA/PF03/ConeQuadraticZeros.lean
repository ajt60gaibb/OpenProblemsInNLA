import NLA.PF03.ConeCrossQuadratics

/-!
C12: complete nonnegativity and real zero-set classification on the whole cone.
All-zero coefficients are included explicitly. Otherwise any nonzero coefficient
selects one group; strict cross pairings force every other group to vanish.
No positive-width, normalized-coefficient, or nonzero-vector premise is added.
Original mathematics: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance.
-/
set_option autoImplicit false
open scoped BigOperators Matrix
noncomputable section
namespace NLA.PF03

theorem cone_quadratic_zeros (x : Fin 7 → ℝ) (hx : x ∈ K) :
    0 ≤ quad quadraticSeed x ∧
      (quad quadraticSeed x = 0 ↔
        ∃ i : Fin 7, ∃ t : ℝ, 0 ≤ t ∧ x = t • seedColumn i) := by
  classical
  obtain ⟨lam, hlam, hxsum⟩ := (K_mem_coordinates x).mp hx
  change x = ∑ i : Fin 7, coneGroup i (lam i) at hxsum
  have hnonneg (i j : Fin 7) :
      0 ≤ bilinear quadraticSeed (coneGroup i (lam i)) (coneGroup j (lam j)) := by
    by_cases hij : i = j
    · subst j
      exact (cone_group_local_kernel i (lam i) (hlam i)).1
    · exact cone_group_cross_nonneg i j hij (lam i) (lam j) (hlam i) (hlam j)
  have hsum : quad quadraticSeed x =
      ∑ i : Fin 7, ∑ j : Fin 7,
        bilinear quadraticSeed (coneGroup i (lam i)) (coneGroup j (lam j)) := by
    rw [hxsum]
    exact cone_quad_sum quadraticSeed (fun i => coneGroup i (lam i))
  constructor
  · rw [hsum]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hnonneg i j))
  · constructor
    · intro hz
      have hzsum := hsum.symm.trans hz
      by_cases hall : ∀ i a, lam i a = 0
      · have hxzero : x = 0 := by
          rw [hxsum]
          simp [coneGroup, hall]
        exact ⟨0, 0, le_rfl, by rw [hxzero, zero_smul]⟩
      · push_neg at hall
        obtain ⟨i, a, hia⟩ := hall
        have hother (j : Fin 7) (hji : j ≠ i) (b : Fin 3) : lam j b = 0 := by
          have hgroupzero := cone_double_sum_term_zero
            (fun r s : Fin 7 =>
              bilinear quadraticSeed (coneGroup r (lam r)) (coneGroup s (lam s)))
            hnonneg hzsum i j
          have hprod := cone_group_cross_zero i j hji.symm
            (lam i) (lam j) (hlam i) (hlam j) hgroupzero a b
          exact (mul_eq_zero.mp hprod).resolve_left hia
        have hgroupother (j : Fin 7) (hji : j ≠ i) : coneGroup j (lam j) = 0 := by
          simp [coneGroup, hother j hji]
        have hxlocal : x = coneGroup i (lam i) := by
          rw [hxsum]
          exact Finset.sum_eq_single i (fun j _ hji => hgroupother j hji) (by simp)
        have hzlocal : quad quadraticSeed (coneGroup i (lam i)) = 0 := by
          rw [← hxlocal]
          exact hz
        obtain ⟨t, ht, hlocal⟩ :=
          (cone_group_local_kernel i (lam i) (hlam i)).2 hzlocal
        exact ⟨i, t, ht, hxlocal.trans hlocal⟩
    · rintro ⟨i, t, _ht, rfl⟩
      rw [cone_quad_smul, seedColumn_quad_zero, mul_zero]

#print axioms cone_quadratic_zeros
#assert_trust kernel cone_quadratic_zeros

end NLA.PF03
