import NLA.TR07.SignedVectors

/-! The averaged filter for the nonsymmetric, regularized transition matrix. -/
noncomputable section
open scoped BigOperators
open Matrix
attribute [local instance] Classical.propDecidable
namespace NLA.TR07

variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

theorem averaged_covariance_filter (p : Law α) (u : α → EuclideanSpace ℝ ι)
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) {s : ℝ} (hs : 0 < s)
    (hcap : (s • diagonal d - covariance p u).PosSemidef) (L : ℕ) :
    p.expect (fun a => ‖((1 - s⁻¹ • (covariance p u * diagonal (fun i => (d i)⁻¹))) ^ L).toEuclideanLin
      (u a)‖ ^ 2) ≤ s / (2 * L + 1) * ∑ i, d i := by
  let S : Matrix ι ι ℝ := diagonal (fun i => Real.sqrt (d i))
  let N : Matrix ι ι ℝ := diagonal (fun i => (Real.sqrt (d i))⁻¹)
  let R := N * covariance p u * N
  let Q := (1 : Matrix ι ι ℝ) - s⁻¹ • R
  let P := (1 : Matrix ι ι ℝ) - s⁻¹ • (covariance p u * diagonal (fun i => (d i)⁻¹))
  have hSN : S * N = 1 := by
    simp only [S, N, diagonal_mul_diagonal]
    simp [Real.sqrt_ne_zero'.mpr (hd _)]
  have hNS : N * S = 1 := by
    simp only [S, N, diagonal_mul_diagonal]
    simp [Real.sqrt_ne_zero'.mpr (hd _)]
  have hSS : S * S = diagonal d := by
    simp only [S, diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← pow_two, Real.sq_sqrt (hd i).le]
  have hNN : N * N = diagonal (fun i => (d i)⁻¹) := by
    simp only [N, diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← pow_two, inv_pow, Real.sq_sqrt (hd i).le]
  have hN : Nᴴ = N := by simp [N]
  have hS : Sᵀ = S := by simp [S]
  have hNR : (N * diagonal d * N) = 1 := by
    rw [← hSS]
    calc
      N * (S * S) * N = (N * S) * (S * N) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hNS, hSN, one_mul]
  have hR : R.PosSemidef := by
    simpa only [R, hN] using (covariance_psd p u).mul_mul_conjTranspose_same N
  have hRcap : (s • (1 : Matrix ι ι ℝ) - R).PosSemidef := by
    have hh := hcap.mul_mul_conjTranspose_same N
    simpa only [hN, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      hNR, R] using hh
  have hQ : Q.IsHermitian := isHermitian_one.sub (hR.isHermitian.smul (IsSelfAdjoint.all _))
  have hQt : Qᵀ = Q := by simpa only [conjTranspose_eq_transpose_of_trivial] using hQ.eq
  have hcomm : Commute R Q := by
    change R * Q = Q * R
    simp [Q, Matrix.mul_sub, Matrix.sub_mul]
  have hPS : P * S = S * Q := by
    dsimp [P, Q, R]
    rw [← hNN]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    congr 1
    calc
      covariance p u * (N * N) * S = covariance p u * N * (N * S) := by simp only [Matrix.mul_assoc]
      _ = covariance p u * N := by rw [hNS, Matrix.mul_one]
      _ = S * (N * covariance p u * N) := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hSN, Matrix.one_mul]
  have hpow : ∀ l : ℕ, P ^ l * S = S * Q ^ l := by
    intro l
    induction l with
    | zero => simp
    | succ l ih => rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hPS,
        Matrix.mul_assoc, ← pow_succ']
  have hCov : covariance p u = S * R * S := by
    dsimp [R]
    simp only [← Matrix.mul_assoc, hSN, Matrix.one_mul]
    rw [Matrix.mul_assoc, hNS, Matrix.mul_one]
  have htrace : (P ^ L * covariance p u * (P ^ L)ᵀ).trace =
      (diagonal d * (R * Q ^ (2 * L))).trace := by
    have hc : P ^ L * covariance p u * (P ^ L)ᵀ =
        (P ^ L * S) * R * (P ^ L * S)ᵀ := by
      rw [hCov, transpose_mul, hS]
      simp only [Matrix.mul_assoc]
    rw [hc, hpow, transpose_mul, transpose_pow, hQt, hS]
    have hp : Q ^ L * R * Q ^ L = R * Q ^ (2 * L) := by
      rw [← (hcomm.pow_right L).eq, Matrix.mul_assoc, ← pow_add, ← two_mul]
    calc
      (S * Q ^ L * R * (Q ^ L * S)).trace =
          (S * (Q ^ L * R * Q ^ L) * S).trace := by simp only [Matrix.mul_assoc]
      _ = (S * (R * Q ^ (2 * L)) * S).trace := by rw [hp]
      _ = (S * S * (R * Q ^ (2 * L))).trace := by rw [trace_mul_cycle]
      _ = _ := by rw [hSS]
  have hbound := weighted_trace_le (spectral_filter_psd hR hs hRcap (2 * L)) d (fun i => (hd i).le)
  rw [← htrace] at hbound
  rw [← covariance_transform, covariance_trace] at hbound
  simpa only [P, Nat.cast_mul, Nat.cast_ofNat] using hbound

def transitionMatrix {k : ℕ} (p : Law α) (u : α → Vec k) (s : ℕ) : Mat k k :=
  (s : ℝ)⁻¹ • (covariance p u * diagonal (fun i => (regDiagonal p u i)⁻¹))

theorem sparse_filter_bound {k s : ℕ} (p : Law α) (u : α → Vec k)
    (hu : ∀ a, SignedVector s (u a)) (hk : 0 < k) (hs : 0 < s) (L : ℕ) :
    p.expect (fun a => ‖((1 - transitionMatrix p u s) ^ L).toEuclideanLin (u a)‖ ^ 2) ≤
      2 * (s : ℝ) ^ 2 / (2 * L + 1) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have h := averaged_covariance_filter p u (regDiagonal p u) (regDiagonal_pos p u hk)
    hs' (covariance_regularized_cap p u hu) L
  rw [sum_regDiagonal p u hu hk] at h
  apply h.trans
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hden : (0 : ℝ) < 2 * L + 1 := by positivity
  apply (le_div_iff₀ hden).mpr
  field_simp
  nlinarith

end NLA.TR07
