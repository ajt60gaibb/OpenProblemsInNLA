import NLA.Proofs.RA10.NuclearNormPSDTrace
import NLA.Proofs.RA10.NuclearNormTriangle
import NLA.Proofs.RA10.NuclearNormHomogeneity
import NLA.Proofs.RA10.NuclearOrthogonalConjugation
import Mathlib.Analysis.Matrix.PosDef

/-! RA-10 source Equation (10): the exact positive-part trace identity for the
frozen all-singular-value nuclear norm. This is a generic dependency; the
source compression identity and final Target are separate obligations. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix

namespace NLA.Proofs.RA10

noncomputable def hermitianPositivePart {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  if hM : M.IsHermitian then
    let U : Matrix (Fin n) (Fin n) ℝ := hM.eigenvectorUnitary
    U * Matrix.diagonal (fun i : Fin n => max (hM.eigenvalues i) 0) * U.transpose
  else 0

private theorem scalar_abs_eq_two_max_sub (x : ℝ) :
    |x| = 2 * max x 0 - x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_left hx]
    ring
  · have hlt : x < 0 := lt_of_not_ge hx
    rw [abs_of_neg hlt, max_eq_right hlt.le]
    ring

private theorem nuclearNorm_diagonal_eq_sum_abs {n : ℕ} (d : Fin n → ℝ) :
    NLA.Statements.RA10.NuclearNorm (Matrix.diagonal d) =
      ∑ i : Fin n, |d i| := by
  classical
  let dp : Fin n → ℝ := fun i => max (d i) 0
  let dn : Fin n → ℝ := fun i => max (-d i) 0
  let s : Fin n → ℝ := fun i => if 0 ≤ d i then 1 else -1
  let S : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal s
  have hsplit : Matrix.diagonal d = Matrix.diagonal dp - Matrix.diagonal dn := by
    rw [Matrix.diagonal_sub]
    congr 1
    funext i
    exact (max_zero_sub_max_neg_zero_eq_self (d i)).symm
  have hdp : Matrix.PosSemidef (Matrix.diagonal dp) :=
    Matrix.PosSemidef.diagonal (fun i => le_max_right (d i) 0)
  have hdn : Matrix.PosSemidef (Matrix.diagonal dn) :=
    Matrix.PosSemidef.diagonal (fun i => le_max_right (-d i) 0)
  have hsquare : ∀ i : Fin n, s i * s i = 1 := by
    intro i
    by_cases hi : 0 ≤ d i <;> simp [s, hi]
  have hStrans : S.transpose = S := Matrix.diagonal_transpose s
  have hSS : S * S = 1 := by
    calc
      S * S = Matrix.diagonal (fun i => s i * s i) :=
        Matrix.diagonal_mul_diagonal s s
      _ = Matrix.diagonal (fun _ => (1 : ℝ)) := by
        congr 1
        funext i
        exact hsquare i
      _ = 1 := Matrix.diagonal_one
  have hSleft : S.transpose * S = 1 := by rw [hStrans, hSS]
  have hSright : S * S.transpose = 1 := by rw [hStrans, hSS]
  have htrace : Matrix.trace (S.transpose * Matrix.diagonal d) =
      ∑ i : Fin n, |d i| := by
    rw [hStrans, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ d i
    · simp [s, hi, abs_of_nonneg hi]
    · have hlt : d i < 0 := lt_of_not_ge hi
      simp [s, hi, abs_of_neg hlt]
  have hlower : (∑ i : Fin n, |d i|) ≤
      NLA.Statements.RA10.NuclearNorm (Matrix.diagonal d) := by
    rw [← htrace]
    exact nuclearNorm_trace_orthogonal_le S (Matrix.diagonal d) hSleft hSright
  have hneg : NLA.Statements.RA10.NuclearNorm (-Matrix.diagonal dn) =
      NLA.Statements.RA10.NuclearNorm (Matrix.diagonal dn) := by
    have hh := nuclearNorm_smul (-1 : ℝ) (Matrix.diagonal dn)
    simpa using hh
  have hupper : NLA.Statements.RA10.NuclearNorm (Matrix.diagonal d) ≤
      Matrix.trace (Matrix.diagonal dp) + Matrix.trace (Matrix.diagonal dn) := by
    rw [hsplit, sub_eq_add_neg]
    calc
      NLA.Statements.RA10.NuclearNorm
          (Matrix.diagonal dp + -Matrix.diagonal dn) ≤
          NLA.Statements.RA10.NuclearNorm (Matrix.diagonal dp) +
            NLA.Statements.RA10.NuclearNorm (-Matrix.diagonal dn) :=
        nuclearNorm_add_le _ _
      _ = Matrix.trace (Matrix.diagonal dp) +
          Matrix.trace (Matrix.diagonal dn) := by
        rw [nuclearNorm_eq_trace_of_posSemidef _ hdp, hneg,
          nuclearNorm_eq_trace_of_posSemidef _ hdn]
  have htraces : Matrix.trace (Matrix.diagonal dp) +
      Matrix.trace (Matrix.diagonal dn) = ∑ i : Fin n, |d i| := by
    rw [Matrix.trace_diagonal, Matrix.trace_diagonal, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [dp, dn]
    by_cases h : 0 ≤ d i
    · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h]
    · have hlt : d i < 0 := lt_of_not_ge h
      simp [max_eq_right hlt.le, max_eq_left (neg_nonneg.mpr hlt.le), abs_of_neg hlt]
  exact le_antisymm (hupper.trans_eq htraces) hlower

theorem nuclearNorm_eq_two_trace_positivePart_sub_trace {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
    NLA.Statements.RA10.NuclearNorm M =
      2 * Matrix.trace (hermitianPositivePart M) - Matrix.trace M := by
  classical
  let U : Matrix (Fin n) (Fin n) ℝ := hM.eigenvectorUnitary
  let d : Fin n → ℝ := hM.eigenvalues
  have hUtU : U.transpose * U = 1 := by
    have hu := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    simpa [U, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hu
  have hUUt : U * U.transpose = 1 := by
    have hu := Unitary.coe_mul_star_self hM.eigenvectorUnitary
    simpa [U, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hu
  have hMdiag : M = U * Matrix.diagonal d * U.transpose := by
    simpa [U, d, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hM.spectral_theorem
  have hpart : hermitianPositivePart M =
      U * Matrix.diagonal (fun i : Fin n => max (d i) 0) * U.transpose := by
    simp only [hermitianPositivePart, dif_pos hM]
    rfl
  have htrace_conj (e : Fin n → ℝ) :
      Matrix.trace (U * Matrix.diagonal e * U.transpose) =
        ∑ i : Fin n, e i := by
    calc
      Matrix.trace (U * Matrix.diagonal e * U.transpose) =
          Matrix.trace (U.transpose * U * Matrix.diagonal e) := by
        rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace (Matrix.diagonal e) := by rw [hUtU, one_mul]
      _ = ∑ i : Fin n, e i := Matrix.trace_diagonal e
  have hnorm : NLA.Statements.RA10.NuclearNorm M =
      ∑ i : Fin n, |d i| := by
    rw [hMdiag, nuclearNorm_orthogonal_conj U (Matrix.diagonal d) hUtU hUUt]
    exact nuclearNorm_diagonal_eq_sum_abs d
  rw [hnorm, hpart, hMdiag, htrace_conj, htrace_conj]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact scalar_abs_eq_two_max_sub (d i)

#assert_trust kernel hermitianPositivePart
#assert_trust kernel nuclearNorm_eq_two_trace_positivePart_sub_trace
#print axioms nuclearNorm_eq_two_trace_positivePart_sub_trace

/-- Public reuse of the proved diagonal nuclear-norm formula. -/
theorem nuclearNorm_diagonal {n : ℕ} (d : Fin n → ℝ) :
    NLA.Statements.RA10.NuclearNorm (Matrix.diagonal d) = ∑ i : Fin n, |d i| :=
  nuclearNorm_diagonal_eq_sum_abs d

#assert_trust kernel nuclearNorm_diagonal

end NLA.Proofs.RA10
