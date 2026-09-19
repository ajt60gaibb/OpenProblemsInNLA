/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

Two concrete orthonormal eigenbases give nonnegative overlap weights with both
marginals equal to one. Expanding the literal matrix trace proves the resulting
double-sum formula. No trace Holder, majorization or norm inequality is assumed.
-/
import NLA.MI24.TraceSpectral

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section
namespace NLA.MI24

def unitaryOverlapWeight {n : ℕ} (U : unitary (Mat n)) (i j : Fin n) : ℝ :=
  Complex.normSq ((U : Mat n) i j)

lemma unitaryOverlapWeight_nonneg {n : ℕ} (U : unitary (Mat n)) (i j : Fin n) :
    0 ≤ unitaryOverlapWeight U i j := Complex.normSq_nonneg _

lemma unitaryOverlapWeight_row {n : ℕ} (U : unitary (Mat n)) (i : Fin n) :
    ∑ j : Fin n, unitaryOverlapWeight U i j = 1 := by
  have h : (((U : Mat n) * (U : Mat n)ᴴ) i i).re = 1 := by
    -- Specialize the unitary star identity to the underlying matrix and
    -- its conjugate-transpose notation before evaluating the diagonal entry.
    rw [show (U : Mat n) * (U : Mat n)ᴴ = 1 from Unitary.coe_mul_star_self U]
    simp only [Matrix.one_apply_eq, Complex.one_re]
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, ← starRingEnd_apply,
    Complex.mul_conj, Complex.re_sum, Complex.ofReal_re, unitaryOverlapWeight] using h

lemma unitaryOverlapWeight_column {n : ℕ} (U : unitary (Mat n)) (j : Fin n) :
    ∑ i : Fin n, unitaryOverlapWeight U i j = 1 := by
  have h : (((U : Mat n)ᴴ * (U : Mat n)) j j).re = 1 := by
    -- Specialize the reverse unitary star identity to the underlying
    -- matrix; this yields the column-weight normalization at entry (j,j).
    rw [show (U : Mat n)ᴴ * (U : Mat n) = 1 from Unitary.coe_star_mul_self U]
    simp only [Matrix.one_apply_eq, Complex.one_re]
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, ← starRingEnd_apply,
    ← Complex.normSq_eq_conj_mul_self, Complex.re_sum, Complex.ofReal_re,
    unitaryOverlapWeight] using h

lemma traceReal_diagonal_unitary {n : ℕ} (U : unitary (Mat n))
    (x y : Fin n → ℝ) :
    traceReal (Matrix.diagonal (fun i => (x i : ℂ)) * (U : Mat n) *
      Matrix.diagonal (fun j => (y j : ℂ)) * (U : Mat n)ᴴ) =
      ∑ i : Fin n, ∑ j : Fin n, x i * y j * unitaryOverlapWeight U i j := by
  unfold traceReal Matrix.trace
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  -- Expose the diagonal entry selected by Matrix.trace/Matrix.diag;
  -- Matrix.mul_apply can then expand precisely this entry.
  change ((Matrix.diagonal (fun i => (x i : ℂ)) * (U : Mat n) *
    Matrix.diagonal (fun j => (y j : ℂ)) * (U : Mat n)ᴴ) i i).re = _
  rw [Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  -- After the diagonal multiplications, expose scalar matrix entries
  -- and complex conjugation so commutative ring arithmetic can regroup them.
  change (((x i : ℂ) * (U : Mat n) i j * (y j : ℂ)) *
    starRingEnd ℂ ((U : Mat n) i j)).re = _
  calc
    _ = (((x i : ℂ) * (y j : ℂ)) *
        ((U : Mat n) i j * starRingEnd ℂ ((U : Mat n) i j))).re := by
      congr 1
      ring
    _ = x i * y j * unitaryOverlapWeight U i j := by
      rw [Complex.mul_conj]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, unitaryOverlapWeight]

lemma traceReal_two_conjugates {n : ℕ} (U V : unitary (Mat n))
    (x y : Fin n → ℝ) :
    traceReal (((U : Mat n) * Matrix.diagonal (fun i => (x i : ℂ)) * (U : Mat n)ᴴ) *
      ((V : Mat n) * Matrix.diagonal (fun j => (y j : ℂ)) * (V : Mat n)ᴴ)) =
      ∑ i : Fin n, ∑ j : Fin n,
        x i * y j * unitaryOverlapWeight (star U * V) i j := by
  let dx : Mat n := Matrix.diagonal (fun i => (x i : ℂ))
  let dy : Mat n := Matrix.diagonal (fun j => (y j : ℂ))
  have htrace :
      (((U : Mat n) * dx * star (U : Mat n)) *
        ((V : Mat n) * dy * star (V : Mat n))).trace =
      (dx * (↑(star U * V) : Mat n) * dy * star (↑(star U * V) : Mat n)).trace := by
    calc
      _ = ((U : Mat n) *
          (dx * star (U : Mat n) * (V : Mat n) * dy * star (V : Mat n))).trace := by
        congr 1
        simp only [mul_assoc]
      _ = ((dx * star (U : Mat n) * (V : Mat n) * dy * star (V : Mat n)) *
          (U : Mat n)).trace := Matrix.trace_mul_comm _ _
      _ = _ := by
        congr 1
        simp only [Submonoid.coe_mul, Unitary.coe_star, star_mul, star_star, mul_assoc]
  -- Expose traceReal and the named spectral decompositions in the goal;
  -- the proved cyclic trace equality htrace then matches literally.
  change (((U : Mat n) * dx * star (U : Mat n)) *
    ((V : Mat n) * dy * star (V : Mat n))).trace.re = _
  rw [htrace]
  exact traceReal_diagonal_unitary (star U * V) x y

lemma traceReal_spectralPower_product {n : ℕ} (P Q : Mat n)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (a b : ℝ) :
    traceReal (spectralPower P a * spectralPower Q b) =
      ∑ i : Fin n, ∑ j : Fin n,
        hP.isHermitian.eigenvalues i ^ a * hQ.isHermitian.eigenvalues j ^ b *
          unitaryOverlapWeight
            (star hP.isHermitian.eigenvectorUnitary * hQ.isHermitian.eigenvectorUnitary) i j := by
  rw [spectralPower_spectral_decomposition P hP a,
    spectralPower_spectral_decomposition Q hQ b]
  exact traceReal_two_conjugates _ _ _ _

lemma unitaryOverlapWeight_marginals {n : ℕ} (U : unitary (Mat n))
    (x y : Fin n → ℝ) (a b : ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, (a * x i + b * y j) * unitaryOverlapWeight U i j) =
      a * (∑ i : Fin n, x i) + b * (∑ j : Fin n, y j) := by
  have hx : (∑ i : Fin n, ∑ j : Fin n, a * x i * unitaryOverlapWeight U i j) =
      a * (∑ i : Fin n, x i) := by
    simp_rw [← Finset.mul_sum, unitaryOverlapWeight_row, mul_one]
    exact (Finset.mul_sum _ _ _).symm
  have hy : (∑ i : Fin n, ∑ j : Fin n, b * y j * unitaryOverlapWeight U i j) =
      b * (∑ j : Fin n, y j) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, unitaryOverlapWeight_column, mul_one]
    exact (Finset.mul_sum _ _ _).symm
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [hx, hy]

end NLA.MI24
