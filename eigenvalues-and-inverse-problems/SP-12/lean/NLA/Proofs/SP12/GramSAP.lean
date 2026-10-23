import NLA.Proofs.SP12.RealLSS
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# SAP from independence of actual earlier nonneighbors

The maximal nonzero column of a symmetric SAP test matrix is supported on the
earlier nonneighbors. Gram kernel equality and independence force that column
to vanish. This is Hall's local upper-zero genericity argument, without a
stronger global general-position requirement.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open NLA.Proofs.SP11
open Matrix

namespace NLA.Proofs.SP12

/-- Gram positivity is the exact nonnegative quadratic form of the frozen target. -/
theorem gram_nonnegativeQuadraticForm {n d : ℕ} (R : Matrix (Fin n) (Fin d) ℝ) :
    NLA.Statements.SP12.NonnegativeQuadraticForm (gram R) := by
  have h := Matrix.posSemidef_self_mul_conjTranspose R
  have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h).2
  intro x
  simpa only [gram, Matrix.conjTranspose_eq_transpose_of_trivial, star_trivial,
    dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using hq x

/-- A real Gram matrix and its row-factor transpose have the same kernel. -/
theorem gram_mulVec_eq_zero_iff {n d : ℕ} (R : Matrix (Fin n) (Fin d) ℝ)
    (x : Fin n → ℝ) : gram R *ᵥ x = 0 ↔ R.transpose *ᵥ x = 0 := by
  constructor
  · intro hx
    apply dotProduct_self_eq_zero.mp
    have h : x ⬝ᵥ (gram R *ᵥ x) = 0 := by rw [hx, dotProduct_zero]
    simpa only [gram, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose] using h
  · intro hx
    rw [gram, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

/-- Simultaneous permutation of both axes preserves the exact frozen SAP. -/
theorem strongArnold_submatrix_equiv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : NLA.Statements.SP12.StrongArnold A) (e : Fin n ≃ Fin n) :
    NLA.Statements.SP12.StrongArnold (A.submatrix e e) := by
  intro X hsym hmul hhad hdiag
  let Y := X.submatrix e.symm e.symm
  have hAY : A * Y = 0 := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M.submatrix e.symm e.symm) hmul
    rw [← Matrix.submatrix_mul_equiv _ _ e.symm e.symm e.symm] at h
    have hback : (A.submatrix e e).submatrix e.symm e.symm = A := by
      ext i j
      simp
    rw [hback] at h
    simpa only [Matrix.submatrix_zero, Pi.zero_apply] using h
  have hY := hA Y (fun i j => hsym (e.symm i) (e.symm j)) hAY
    (fun i j => by simpa [Y] using hhad (e.symm i) (e.symm j))
    (fun i => hdiag (e.symm i))
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M.submatrix e e) hY
  have hback : Y.submatrix e e = X := by
    ext i j
    simp [Y]
  rw [hback] at h
  simpa only [Matrix.submatrix_zero, Pi.zero_apply] using h

/-- Reindexing the rows of a Gram factor preserves SAP. -/
theorem strongArnold_gram_relabel {n d : ℕ} (R : Matrix (Fin n) (Fin d) ℝ)
    (e : Fin n ≃ Fin n) (h : NLA.Statements.SP12.StrongArnold (gram R)) :
    NLA.Statements.SP12.StrongArnold (gram (fun i => R (e i))) := by
  change NLA.Statements.SP12.StrongArnold ((gram R).submatrix e e)
  exact strongArnold_submatrix_equiv _ h e

/-- Local earlier-nonneighbor independence is enough for the full SAP. -/
theorem gram_strongArnold_of_prior_linearIndependent {n d : ℕ}
    (G : SimpleGraph (Fin n)) (R : Matrix (Fin n) (Fin d) ℝ)
    (hpattern : NLA.Statements.SP12.HasPattern G (gram R))
    (hLI : ∀ j, LinearIndependent ℝ (fun s => R (priorVertex G j s))) :
    NLA.Statements.SP12.StrongArnold (gram R) := by
  classical
  intro X hsym hAX hhad hdiag
  by_contra hX
  have hentry : ∃ i j, X i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hX
    ext i j
    exact h i j
  let S : Finset (Fin n) := Finset.univ.filter (fun j => ∃ i, X i j ≠ 0)
  have hSne : S.Nonempty := by
    obtain ⟨i, j, hij⟩ := hentry
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hij⟩⟩
  let j := S.max' hSne
  have hj : j ∈ S := Finset.max'_mem S hSne
  have hlater (i : Fin n) (hji : j < i) : ∀ a, X a i = 0 := by
    intro a
    by_contra ha
    have hi : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, ha⟩
    exact (not_le_of_gt hji) (Finset.le_max' S i hi)
  let t : Finset (Fin n) := Finset.univ.filter (fun i => X i j ≠ 0)
  have hsupport (i : Fin n) (hi : i ∈ t) : i ∈ Set.range (priorVertex G j) := by
    have hij : X i j ≠ 0 := (Finset.mem_filter.mp hi).2
    have hlt : i < j := by
      by_contra hnot
      rcases (le_of_not_gt hnot).eq_or_lt with heq | hgt
      · subst i
        exact hij (hdiag j)
      · exact hij ((hsym i j).trans (hlater i hgt j))
    have hnot : ¬ G.Adj j i := by
      intro hadj
      have hnonzero := (hpattern.2 i j (ne_of_lt hlt)).mpr hadj.symm
      exact (mul_ne_zero hnonzero hij) (hhad i j)
    obtain ⟨s, hs⟩ := List.mem_iff_get.mp ((mem_priorNonneighbors G i j).mpr ⟨hlt, hnot⟩)
    exact ⟨s, hs⟩
  have hker : gram R *ᵥ (fun i => X i j) = 0 := by
    ext i
    exact congrFun (congrFun hAX i) j
  have hsum : (∑ i, X i j • R i) = 0 := by
    have h := (gram_mulVec_eq_zero_iff R (fun i => X i j)).mp hker
    rwa [Matrix.mulVec_transpose, Matrix.vecMul_eq_sum] at h
  have hsumt : (∑ i ∈ t, X i j • R i) = 0 := by
    rw [← hsum]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hz : X i j = 0 := by simpa only [t, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi
    simp only [hz, zero_smul]
  have hlocal : LinearIndepOn ℝ R (Set.range (priorVertex G j)) :=
    (linearIndepOn_range_iff (priorVertex_strictMono G j).injective R).mpr (hLI j)
  have hc := (linearIndepOn_iff'.mp hlocal) t (fun i => X i j) hsupport hsumt
  obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hj).2
  exact hi (hc i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))

#assert_trust kernel gram_nonnegativeQuadraticForm
#assert_trust kernel gram_mulVec_eq_zero_iff
#assert_trust kernel strongArnold_submatrix_equiv
#assert_trust kernel strongArnold_gram_relabel
#assert_trust kernel gram_strongArnold_of_prior_linearIndependent
#print axioms strongArnold_submatrix_equiv
#print axioms gram_nonnegativeQuadraticForm
#print axioms gram_strongArnold_of_prior_linearIndependent

end NLA.Proofs.SP12
