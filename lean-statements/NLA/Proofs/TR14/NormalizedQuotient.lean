import NLA.Proofs.TR14.ApolarMinimal
import Mathlib.RingTheory.AdjoinRoot

/-!
Conditional affine quotient foundation for a monic minimal apolar form.
Global GL₂ chart transport and the TR-14 all-width target remain open.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Polynomial

namespace NLA.Proofs.TR14

/-- The unique linear functional on the monic polynomial quotient specified
by the first `g.natDegree` moments. -/
noncomputable def quotientMomentFunctional {D : ℕ}
    (h : Fin (D + 1) → ℂ) (g : Polynomial ℂ)
    (hg : g.Monic) (hrD : g.natDegree ≤ D) :
    AdjoinRoot g →ₗ[ℂ] ℂ :=
  (AdjoinRoot.powerBasis' hg).basis.constr ℂ
    (fun i => h ⟨i.val, by
      have hi := i.isLt
      change i.val < g.natDegree at hi
      omega⟩)

/-- The defining initial moment values, including the first and last basis
indices. -/
theorem quotientMomentFunctional_initial {D : ℕ}
    (h : Fin (D + 1) → ℂ) (g : Polynomial ℂ)
    (hg : g.Monic) (hrD : g.natDegree ≤ D)
    (i : Fin g.natDegree) :
    quotientMomentFunctional h g hg hrD ((AdjoinRoot.root g) ^ i.val) =
      h ⟨i.val, by have hi := i.isLt; omega⟩ := by
  unfold quotientMomentFunctional
  have hb := (AdjoinRoot.powerBasis' hg).basis.constr_basis ℂ
    (fun j => h ⟨j.val, by
      have hj := j.isLt
      change j.val < g.natDegree at hj
      omega⟩) i
  have heq : (AdjoinRoot.powerBasis' hg).basis i =
      (AdjoinRoot.root g) ^ i.val :=
    (AdjoinRoot.powerBasis' hg).basis_eq_pow i
  rw [heq] at hb
  exact hb

/-- The quotient has exactly the degree of the normalized polynomial. -/
theorem quotient_finrank (g : Polynomial ℂ) (hg : g.Monic) :
    Module.finrank ℂ (AdjoinRoot g) = g.natDegree :=
  (AdjoinRoot.powerBasis' hg).finrank

private theorem quotient_root_relation (g : Polynomial ℂ) (hg : g.Monic) :
    (AdjoinRoot.root g) ^ g.natDegree =
      -(∑ i ∈ Finset.range g.natDegree,
        g.coeff i • (AdjoinRoot.root g) ^ i) := by
  have hz : Polynomial.aeval (AdjoinRoot.root g) g = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ] at hz
  rw [hg.coeff_natDegree, one_smul] at hz
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hz)

private theorem quotient_root_recurrence (g : Polynomial ℂ) (hg : g.Monic)
    (k : ℕ) :
    (AdjoinRoot.root g) ^ (k + g.natDegree) =
      -(∑ i ∈ Finset.range g.natDegree,
        g.coeff i • (AdjoinRoot.root g) ^ (k + i)) := by
  calc
    (AdjoinRoot.root g) ^ (k + g.natDegree) =
        (AdjoinRoot.root g) ^ g.natDegree * (AdjoinRoot.root g) ^ k := by
          rw [add_comm k g.natDegree, pow_add]
    _ = -(∑ i ∈ Finset.range g.natDegree,
        g.coeff i • (AdjoinRoot.root g) ^ i) * (AdjoinRoot.root g) ^ k := by
          rw [quotient_root_relation g hg]
    _ = -(∑ i ∈ Finset.range g.natDegree,
        g.coeff i • (AdjoinRoot.root g) ^ (k + i)) := by
          simp [Finset.mul_sum, pow_add, mul_comm]

private theorem quotient_functional_recurrence {D : ℕ}
    (h : Fin (D + 1) → ℂ) (g : Polynomial ℂ)
    (hg : g.Monic) (hrD : g.natDegree ≤ D) (k : ℕ) :
    quotientMomentFunctional h g hg hrD
        ((AdjoinRoot.root g) ^ (k + g.natDegree)) =
      -(∑ i : Fin g.natDegree, g.coeff i.val *
        quotientMomentFunctional h g hg hrD
          ((AdjoinRoot.root g) ^ (k + i.val))) := by
  have hrel := congrArg
    (fun x : AdjoinRoot g => quotientMomentFunctional h g hg hrD x)
    (quotient_root_recurrence g hg k)
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => g.coeff i *
      quotientMomentFunctional h g hg hrD
        ((AdjoinRoot.root g) ^ (k + i)))]
  simpa only [map_neg, map_sum, map_smul, smul_eq_mul] using hrel

/-- Exact recurrence in the normalized affine chart. It is the monic form
of the frozen apolar equations, at every shift through `D - g.natDegree`. -/
def MonicMomentRecurrence {D : ℕ} (h : Fin (D + 1) → ℂ)
    (g : Polynomial ℂ) : Prop :=
  ∀ k : ℕ, ∀ hk : k + g.natDegree ≤ D,
    h ⟨k + g.natDegree, by omega⟩ =
      -(∑ i : Fin g.natDegree, g.coeff i.val *
        h ⟨k + i.val, by have hi := i.isLt; omega⟩)

/-- The exact finite apolar convolution supplies the normalized recurrence;
the final `i = g.natDegree` coefficient is one by monicity. -/
theorem monicMomentRecurrence_of_apolar {D : ℕ}
    (h : Fin (D + 1) → ℂ) (g : Polynomial ℂ)
    (hg : g.Monic) (hrD : g.natDegree ≤ D)
    (hAp : IsApolar h g.natDegree hrD
      (fun i : Fin (g.natDegree + 1) => g.coeff i.val)) :
    MonicMomentRecurrence h g := by
  intro k hk
  have hkv : k < D - g.natDegree + 1 := by omega
  have hap : (∑ i : Fin (g.natDegree + 1),
      g.coeff i.val * h ⟨i.val + k, by
        have hi := i.isLt
        omega⟩) = 0 := by
    have hv := congrFun hAp (⟨k, hkv⟩ : Fin (D - g.natDegree + 1))
    simpa [IsApolar, apolarMap] using hv
  rw [Fin.sum_univ_castSucc] at hap
  simp only [Fin.val_castSucc, Fin.val_last, hg.coeff_natDegree, one_mul] at hap
  change h ⟨k + g.natDegree, by omega⟩ =
    -(∑ i : Fin g.natDegree, g.coeff i.val *
      h ⟨k + i.val, by have hi := i.isLt; omega⟩)
  apply eq_neg_of_add_eq_zero_left
  simpa only [add_comm, Nat.add_comm] using hap

/-- In a monic quotient, the exact apolar recurrence propagates the
functional's initial values through **all** available moments. -/
theorem quotientMomentFunctional_all {D : ℕ}
    (h : Fin (D + 1) → ℂ) (g : Polynomial ℂ)
    (hg : g.Monic) (hrD : g.natDegree ≤ D)
    (hrec : MonicMomentRecurrence h g) :
    ∀ j : Fin (D + 1),
      quotientMomentFunctional h g hg hrD
        ((AdjoinRoot.root g) ^ j.val) = h j := by
  have hall : ∀ t : ℕ, ∀ ht : t ≤ D,
      quotientMomentFunctional h g hg hrD
        ((AdjoinRoot.root g) ^ t) = h ⟨t, by omega⟩ := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        intro ht
        by_cases hsmall : t < g.natDegree
        · simpa using quotientMomentFunctional_initial h g hg hrD
            (⟨t, hsmall⟩ : Fin g.natDegree)
        · let k := t - g.natDegree
          have hkr : k + g.natDegree = t := by dsimp [k]; omega
          have hkD : k + g.natDegree ≤ D := by omega
          have hstep : quotientMomentFunctional h g hg hrD
              ((AdjoinRoot.root g) ^ (k + g.natDegree)) =
              h ⟨k + g.natDegree, by omega⟩ := by
            rw [quotient_functional_recurrence h g hg hrD k]
            rw [hrec k hkD]
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            have hprev : k + i.val < t := by
              have hii := i.isLt
              omega
            have hbound : k + i.val ≤ D := by omega
            rw [ih (k + i.val) hprev hbound]
          simpa only [hkr] using hstep
  intro j
  exact hall j.val (Nat.le_of_lt_succ j.isLt)

/-- Conditional normalized quotient: a monic apolar polynomial defines a
degree-`g.natDegree` algebra and a functional matching every supplied
moment through degree `D`. Minimality and Frobenius are separate obligations. -/
theorem normalized_quotient_all_moments {D : ℕ}
    (h : Fin (D + 1) → ℂ) (g : Polynomial ℂ)
    (hg : g.Monic) (hrD : g.natDegree ≤ D)
    (hAp : IsApolar h g.natDegree hrD
      (fun i : Fin (g.natDegree + 1) => g.coeff i.val)) :
    ∃ Λ : AdjoinRoot g →ₗ[ℂ] ℂ,
      Module.finrank ℂ (AdjoinRoot g) = g.natDegree ∧
      ∀ j : Fin (D + 1), Λ ((AdjoinRoot.root g) ^ j.val) = h j := by
  refine ⟨quotientMomentFunctional h g hg hrD, quotient_finrank g hg, ?_⟩
  exact quotientMomentFunctional_all h g hg hrD
    (monicMomentRecurrence_of_apolar h g hg hrD hAp)

#assert_trust kernel quotientMomentFunctional
#assert_trust kernel quotientMomentFunctional_initial
#assert_trust kernel quotient_finrank
#assert_trust kernel quotient_root_relation
#assert_trust kernel quotient_root_recurrence
#assert_trust kernel quotient_functional_recurrence
#assert_trust kernel MonicMomentRecurrence
#assert_trust kernel monicMomentRecurrence_of_apolar
#assert_trust kernel quotientMomentFunctional_all
#assert_trust kernel normalized_quotient_all_moments
#print axioms normalized_quotient_all_moments
#print axioms quotientMomentFunctional_initial

end NLA.Proofs.TR14
