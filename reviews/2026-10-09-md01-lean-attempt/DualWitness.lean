import Mathlib
import Mathlib.Analysis.Matrix.Order

open scoped MatrixOrder
open Matrix

namespace MD01Dual

/-- The trace pairing of two real positive semidefinite matrices is nonnegative. -/
theorem trace_mul_nonneg {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [hC, star_eq_conjTranspose]
  rw [Matrix.trace_mul_cycle' A Cᴴ C]
  rw [← Matrix.mul_assoc]
  exact (hA.mul_mul_conjTranspose_same C).trace_nonneg

#print axioms trace_mul_nonneg

/-- Weak duality for the trace-normalized theta SDP. On each nonedge (and on the
diagonal), the dual matrix entry is one. -/
theorem dual_weak_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (X M : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (hX : X.PosSemidef) (htr : X.trace = 1)
    (hedgeX : ∀ i j, G.Adj i j → X i j = 0)
    (hM : ∀ i j, ¬ G.Adj i j → M i j = 1)
    (hY : (t • (1 : Matrix (Fin n) (Fin n) ℝ) - M).PosSemidef) :
    (∑ i, ∑ j, X i j) ≤ t := by
  classical
  have hsym (i j : Fin n) : X i j = X j i := by
    simpa using congrFun (congrFun hX.isHermitian j) i
  have hentry (i j : Fin n) : M i j * X j i = X i j := by
    by_cases hij : G.Adj i j
    · simp [hedgeX i j hij, hedgeX j i ((G.adj_comm i j).mp hij)]
    · rw [hM i j hij, one_mul]
      exact (hsym i j).symm
  have hMX : (M * X).trace = ∑ i, ∑ j, X i j := by
    simp [Matrix.trace, Matrix.mul_apply, hentry]
  have hnonneg := trace_mul_nonneg _ _ hY hX
  have hYtrace : ((t • (1 : Matrix (Fin n) (Fin n) ℝ) - M) * X).trace =
      t - (∑ i, ∑ j, X i j) := by
    simp [Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_smul, htr, hMX]
  linarith

#print axioms dual_weak_bound

/-- A positive semidefinite target matrix with unit diagonal and a fixed negative
nonedge value bounds every feasible theta objective by `1 + 1 / a`. This is the
abstract rescaling step behind the paper's Definition 2.5. -/
theorem theta_upper_of_rescaled_witness {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Matrix (Fin n) (Fin n) ℝ) (a : ℝ)
    (ha : 0 < a) (hW : W.PosSemidef)
    (hdiag : ∀ i, W i i = 1)
    (hnonedge : ∀ i j, i ≠ j → ¬ G.Adj i j → W i j = -a)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef)
    (htr : X.trace = 1) (hedgeX : ∀ i j, G.Adj i j → X i j = 0) :
    (∑ i, ∑ j, X i j) ≤ 1 + 1 / a := by
  classical
  let s : ℝ := 1 / a
  let M : Matrix (Fin n) (Fin n) ℝ := (1 + s) • 1 - s • W
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hY : ((1 + s) • (1 : Matrix (Fin n) (Fin n) ℝ) - M).PosSemidef := by
    have heq : (1 + s) • (1 : Matrix (Fin n) (Fin n) ℝ) - M = s • W := by
      simp [M]
    rw [heq]
    exact hW.smul hs
  have hM : ∀ i j, ¬ G.Adj i j → M i j = 1 := by
    intro i j hij
    by_cases heq : i = j
    · subst j
      simp [M, hdiag i]
    · simp [M, heq, hnonedge i j heq hij, s]
      field_simp
  simpa [s] using dual_weak_bound G X M (1 + s) hX htr hedgeX hM hY

#print axioms theta_upper_of_rescaled_witness

/-- The same dual witness bounds the supremum in the trace-normalized SDP,
provided its feasible set is nonempty. -/
theorem theta_sup_le_of_rescaled_witness {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Matrix (Fin n) (Fin n) ℝ) (a : ℝ)
    (ha : 0 < a) (hW : W.PosSemidef)
    (hdiag : ∀ i, W i i = 1)
    (hnonedge : ∀ i j, i ≠ j → ¬ G.Adj i j → W i j = -a)
    (hfeas : Set.Nonempty {v : ℝ | ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X.PosSemidef ∧ X.trace = 1 ∧
      (∀ i j, G.Adj i j → X i j = 0) ∧
      v = ∑ i, ∑ j, X i j}) :
    sSup {v : ℝ | ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X.PosSemidef ∧ X.trace = 1 ∧
      (∀ i j, G.Adj i j → X i j = 0) ∧
      v = ∑ i, ∑ j, X i j} ≤ 1 + 1 / a := by
  apply csSup_le hfeas
  rintro v ⟨X, hX, htr, hedgeX, rfl⟩
  exact theta_upper_of_rescaled_witness G W a ha hW hdiag hnonedge X hX htr hedgeX

#print axioms theta_sup_le_of_rescaled_witness

/-- The zero-diagonal, ±1 adjacency matrix used in Definition 2.3. -/
noncomputable def signedAdj {n : ℕ} (G : SimpleGraph (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact fun i j => if i = j then 0 else if G.Adj i j then 1 else -1

/-- Definition 2.5's target-matrix conditions yield the corresponding theta
upper bound. The hard part is constructing such a PSD matrix with `a` near
`1 / sqrt n`; this lemma assumes the matrix already exists. -/
theorem theta_sup_le_of_target_matrix {n : ℕ} (G : SimpleGraph (Fin n))
    (R : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (ha : 0 < a)
    (hRdiag : ∀ i, R i i = 0)
    (hRnonedge : ∀ i j, ¬ G.Adj i j → R i j = 0)
    (hW : ((1 : Matrix (Fin n) (Fin n) ℝ) + a • signedAdj G + R).PosSemidef)
    (hfeas : Set.Nonempty {v : ℝ | ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X.PosSemidef ∧ X.trace = 1 ∧
      (∀ i j, G.Adj i j → X i j = 0) ∧
      v = ∑ i, ∑ j, X i j}) :
    sSup {v : ℝ | ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X.PosSemidef ∧ X.trace = 1 ∧
      (∀ i j, G.Adj i j → X i j = 0) ∧
      v = ∑ i, ∑ j, X i j} ≤ 1 + 1 / a := by
  classical
  apply theta_sup_le_of_rescaled_witness G (1 + a • signedAdj G + R) a ha hW
  · intro i
    simp [signedAdj, hRdiag i]
  · intro i j hij hnon
    simp [signedAdj, hij, hnon, hRnonedge i j hnon]
  · exact hfeas

#print axioms theta_sup_le_of_target_matrix

end MD01Dual
