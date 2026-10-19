import NLA.Proofs.TR14.NormalizedQuotient

/-! Exact uniqueness and power-sum solutions of the literal finite moment
recurrence used in the binary Vandermonde reconstruction. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial
open scoped BigOperators Polynomial
noncomputable section

/-- Initial moments below the polynomial degree determine every available
moment of an actual monic recurrence. Degree zero and empty recurrence ranges
retain their literal meanings. -/
theorem momentRecurrence_unique {D : ℕ}
    (h h' : Fin (D + 1) → ℂ) (P : ℂ[X])
    (hrec : MonicMomentRecurrence h P) (hrec' : MonicMomentRecurrence h' P)
    (hinit : ∀ j : Fin (D + 1), j.val < P.natDegree → h j = h' j) : h = h' := by
  have hall : ∀ t : ℕ, ∀ ht : t ≤ D, h ⟨t, by omega⟩ = h' ⟨t, by omega⟩ := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro ht
      by_cases hsmall : t < P.natDegree
      · exact hinit ⟨t, by omega⟩ hsmall
      · let k := t - P.natDegree
        have hkt : k + P.natDegree = t := by dsimp [k]; omega
        have hkD : k + P.natDegree ≤ D := by omega
        have hstep : h ⟨k + P.natDegree, by omega⟩ =
            h' ⟨k + P.natDegree, by omega⟩ := by
          rw [hrec k hkD, hrec' k hkD]
          congr 1
          apply Finset.sum_congr rfl
          intro i _hi
          have hprev : k + i.val < t := by have hi := i.isLt; omega
          rw [ih (k + i.val) hprev (by omega)]
        simpa only [hkt] using hstep
  funext j
  exact hall j.val (by omega)

/-- Actual roots of P give the actual monic recurrence for every weighted
finite sum of their powers, at every available shift. -/
theorem powerSum_monicMomentRecurrence {D v : ℕ}
    (P : ℂ[X]) (hmonic : P.Monic) (nodes : Fin v → ℂ)
    (hz : ∀ i, P.eval (nodes i) = 0) (c : Fin v → ℂ) :
    MonicMomentRecurrence
      (fun j : Fin (D + 1) => ∑ i, c i * nodes i ^ j.val) P := by
  have hroot (i : Fin v) : nodes i ^ P.natDegree =
      -(∑ j : Fin P.natDegree, P.coeff j.val * nodes i ^ j.val) := by
    have heq := hz i
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ] at heq
    simp only [hmonic.coeff_natDegree, one_mul] at heq
    apply eq_neg_of_add_eq_zero_left
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => P.coeff j * nodes i ^ j)]
    simpa only [add_comm] using heq
  intro k _hk
  change (∑ i : Fin v, c i * nodes i ^ (k + P.natDegree)) =
    -(∑ j : Fin P.natDegree, P.coeff j.val *
      (∑ i : Fin v, c i * nodes i ^ (k + j.val)))
  simp_rw [pow_add, hroot, mul_neg, Finset.mul_sum]
  simp only [Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro i _hi
  ring

#assert_trust kernel momentRecurrence_unique
#assert_trust kernel powerSum_monicMomentRecurrence
#print axioms momentRecurrence_unique
#print axioms powerSum_monicMomentRecurrence

end
end NLA.Proofs.TR14
