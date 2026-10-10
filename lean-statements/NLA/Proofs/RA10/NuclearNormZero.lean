import NLA.Statements.RA10

/-! RA-10 Gate 1b: the literal frozen sum of the first `n` singular values
is nonnegative and vanishes exactly at the zero matrix. This does not prove
the frozen constant-eleven transfer target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

theorem nuclearNorm_nonneg {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ NLA.Statements.RA10.NuclearNorm M := by
  unfold NLA.Statements.RA10.NuclearNorm
  exact Finset.sum_nonneg (fun i _ => (Matrix.toEuclideanLin M).singularValues_nonneg i.val)

theorem nuclearNorm_eq_zero_iff {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.NuclearNorm M = 0 ↔ M = 0 := by
  constructor
  · intro hzero
    have hterm (i : Fin n) : (Matrix.toEuclideanLin M).singularValues i.val = 0 := by
      have hsum :
          (∑ i : Fin n, (Matrix.toEuclideanLin M).singularValues i.val) = 0 := hzero
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => (Matrix.toEuclideanLin M).singularValues_nonneg i.val)).mp hsum i
        (Finset.mem_univ i)
    have hall : (Matrix.toEuclideanLin M).singularValues = 0 := by
      ext j
      by_cases hj : j < n
      · simpa using hterm ⟨j, hj⟩
      · have hcut : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) ≤ j := by
          rw [finrank_euclideanSpace_fin]
          exact Nat.le_of_not_gt hj
        simpa using (Matrix.toEuclideanLin M).singularValues_of_finrank_le hcut
    have hmap : Matrix.toEuclideanLin M = 0 :=
      (Matrix.toEuclideanLin M).singularValues_eq_zero_iff.mp hall
    apply Matrix.toEuclideanLin.injective
    simpa using hmap
  · intro hM
    subst M
    simp [NLA.Statements.RA10.NuclearNorm]

#assert_trust kernel nuclearNorm_nonneg
#assert_trust kernel nuclearNorm_eq_zero_iff
#print axioms nuclearNorm_eq_zero_iff

end NLA.Proofs.RA10
