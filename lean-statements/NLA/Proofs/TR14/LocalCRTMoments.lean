import NLA.Proofs.TR14.LocalCRTFunctional

/-!
Exact all-moment and zero-based Hankel-coordinate transfer from the monic
quotient functional to every truncated CRT factor. This uses all supplied
moments through `D`, not just the power-basis prefix.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open NLA.Statements.TR14 Polynomial
open scoped BigOperators Polynomial
noncomputable section

/-- Exact CRT formula for every supplied moment through `D`, given the
actual all-moment identity of the quotient functional. -/
theorem localCRT_moments_of_all {D : ℕ}
    (h : Fin (D + 1) → ℂ) (g : Polynomial ℂ) (hg : g.Monic)
    (hrD : g.natDegree ≤ D)
    (hall : ∀ j : Fin (D + 1),
      quotientMomentFunctional h g hg hrD ((AdjoinRoot.root g) ^ j.val) = h j)
    (j : Fin (D + 1)) :
    h j = ∑ α : LocalRootIndex g,
      localCRTComponent g hg (quotientMomentFunctional h g hg hrD) α
        ((algebraMap ℂ (LocalTruncated (localRootMultiplicity g α)) α.val +
          localRoot (localRootMultiplicity g α)) ^ j.val) := by
  calc
    h j = quotientMomentFunctional h g hg hrD
        ((AdjoinRoot.root g) ^ j.val) := (hall j).symm
    _ = ∑ α : LocalRootIndex g,
        localCRTComponent g hg (quotientMomentFunctional h g hg hrD) α
          (localCRTEquiv g hg ((AdjoinRoot.root g) ^ j.val) α) :=
            localCRTComponent_sum g hg _ _
    _ = ∑ α : LocalRootIndex g,
        localCRTComponent g hg (quotientMomentFunctional h g hg hrD) α
          ((algebraMap ℂ (LocalTruncated (localRootMultiplicity g α)) α.val +
            localRoot (localRootMultiplicity g α)) ^ j.val) := by
      apply Finset.sum_congr rfl
      intro α _
      rw [localCRTEquiv_root_pow]

/-- Frozen apolarity proves the all-moment premise; it is not an added
assumption on the final numerical target. -/
theorem localCRT_moments_of_apolar {D : ℕ}
    (h : Fin (D + 1) → ℂ) (g : Polynomial ℂ) (hg : g.Monic)
    (hrD : g.natDegree ≤ D)
    (hAp : IsApolar h g.natDegree hrD
      (fun i : Fin (g.natDegree + 1) => g.coeff i.val))
    (j : Fin (D + 1)) :
    h j = ∑ α : LocalRootIndex g,
      localCRTComponent g hg (quotientMomentFunctional h g hg hrD) α
        ((algebraMap ℂ (LocalTruncated (localRootMultiplicity g α)) α.val +
          localRoot (localRootMultiplicity g α)) ^ j.val) :=
  localCRT_moments_of_all h g hg hrD
    (quotientMomentFunctional_all h g hg hrD
      (monicMomentRecurrence_of_apolar h g hg hrD hAp)) j

/-- Exact zero-based Hankel entries are sums of local product evaluations;
this includes all empty-mode and zero-degree indexing endpoints. -/
theorem localCRT_hankel_of_apolar {m q : ℕ}
    (h : Fin (m * q + 1) → ℂ) (g : Polynomial ℂ) (hg : g.Monic)
    (hrD : g.natDegree ≤ m * q)
    (hAp : IsApolar h g.natDegree hrD
      (fun i : Fin (g.natDegree + 1) => g.coeff i.val))
    (i : Fin m → Fin (q + 1)) :
    Hankel h i = ∑ α : LocalRootIndex g,
      localCRTComponent g hg (quotientMomentFunctional h g hg hrD) α
        (∏ k : Fin m,
          (algebraMap ℂ (LocalTruncated (localRootMultiplicity g α)) α.val +
            localRoot (localRootMultiplicity g α)) ^ (i k).val) := by
  change h (HankelIndex i) = _
  rw [localCRT_moments_of_apolar h g hg hrD hAp (HankelIndex i)]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

#assert_trust kernel localCRT_moments_of_all
#assert_trust kernel localCRT_moments_of_apolar
#assert_trust kernel localCRT_hankel_of_apolar
#print axioms localCRT_hankel_of_apolar

end
end NLA.Proofs.TR14
