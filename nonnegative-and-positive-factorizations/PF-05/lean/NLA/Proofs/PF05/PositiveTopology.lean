import NLA.Proofs.PF05.Basic
import Mathlib.Tactic

/-! Positive definite aggregate factors in a rank-three size-two PSD
factorization. These coercive matrices are the first algebraic input for
proving that a congruence orbit is closed in the factorization fiber. -/
set_option autoImplicit false

namespace NLA.Proofs.PF05.PositiveTopology
open NLA.Statements.PF05
open Matrix

abbrev Sym2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev Vec2 := Fin 2 → ℝ
private def outer (v : Vec2) : Sym2 := Matrix.vecMulVec v v

private theorem outer_ne_zero {v : Vec2} (hv : v ≠ 0) : outer v ≠ 0 := by
  intro h
  have h0 : v 0 = 0 := by
    have hh := congrArg (fun M : Sym2 => M 0 0) h
    simp [outer, Matrix.vecMulVec_apply] at hh
    nlinarith [sq_nonneg (v 0)]
  have h1 : v 1 = 0 := by
    have hh := congrArg (fun M : Sym2 => M 1 1) h
    simp [outer, Matrix.vecMulVec_apply] at hh
    nlinarith [sq_nonneg (v 1)]
  apply hv
  funext i
  fin_cases i <;> simp [h0,h1]

private theorem trace_mul_outer_eq_qform (A : Sym2) (v : Vec2) :
    Matrix.trace (A * outer v) = v ⬝ᵥ (A *ᵥ v) := by
  simp [outer, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mulVec,
    Matrix.vecMulVec_apply, dotProduct, Fin.sum_univ_two]
  ring

/-- A finite PSD family whose trace pairings separate symmetric matrices
has a positive definite sum. -/
theorem sum_posDef_of_trace_separating {n : ℕ}
    (X : Fin n → Sym2)
    (hPSD : ∀ i, PositiveSemidefinite (X i))
    (hsep : ∀ C : Sym2, Symmetric C →
      (∀ i, Matrix.trace (X i * C) = 0) → C = 0) :
    (∑ i, X i).PosDef := by
  have hP : (∑ i, X i).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ
      (fun i _ => (NLA.Proofs.PF05.psd_iff_posSemidef (X i)).mp (hPSD i))
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hP.1
  intro v hv
  have hnonneg : ∀ i : Fin n, 0 ≤ v ⬝ᵥ (X i *ᵥ v) := by
    intro i
    exact (Matrix.posSemidef_iff_dotProduct_mulVec.mp
      ((NLA.Proofs.PF05.psd_iff_posSemidef (X i)).mp (hPSD i))).2 v
  have hsum : v ⬝ᵥ ((∑ i, X i) *ᵥ v) = ∑ i, v ⬝ᵥ (X i *ᵥ v) := by
    simp [dotProduct, Matrix.mulVec, Matrix.sum_apply, Finset.mul_sum,
      Finset.sum_mul, Finset.sum_comm]
  have htotal : 0 ≤ v ⬝ᵥ ((∑ i, X i) *ᵥ v) :=
    (Matrix.posSemidef_iff_dotProduct_mulVec.mp hP).2 v
  by_contra hn
  have hzero : ∑ i, v ⬝ᵥ (X i *ᵥ v) = 0 := by
    have hle : v ⬝ᵥ ((∑ i, X i) *ᵥ v) ≤ 0 := le_of_not_gt hn
    linarith [hsum]
  have horth : ∀ i, Matrix.trace (X i * outer v) = 0 := by
    intro i
    rw [trace_mul_outer_eq_qform]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hzero i (Finset.mem_univ i)
  have hC : Symmetric (outer v) := by
    intro i j
    simp [outer, Matrix.vecMulVec_apply, mul_comm]
  have hout : outer v = 0 := hsep (outer v) hC horth
  exact outer_ne_zero hv hout

/-- The sum of the row factors is positive definite at ordinary rank three. -/
theorem sum_rows_posDef {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Sym2) (B : Fin q → Sym2)
    (hfact : Factorization M A B) (hrank : M.rank = 3) :
    (∑ i, A i).PosDef := by
  apply sum_posDef_of_trace_separating A hfact.1
  intro C hC horth
  exact NLA.Proofs.PF05.trace_pairing_left_nondegenerate_of_rank_three
    M A B hfact hrank C hC horth

/-- The sum of the column factors is positive definite at ordinary rank three. -/
theorem sum_columns_posDef {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Sym2) (B : Fin q → Sym2)
    (hfact : Factorization M A B) (hrank : M.rank = 3) :
    (∑ j, B j).PosDef := by
  apply sum_posDef_of_trace_separating B hfact.2.1
  intro C hC horth
  apply NLA.Proofs.PF05.trace_pairing_right_nondegenerate_of_rank_three
    M A B hfact hrank C hC
  intro j
  rw [Matrix.trace_mul_comm]
  exact horth j

/-- Positive definiteness of a congruence forces the congruence matrix to be
invertible, regardless of the source matrix. -/
theorem det_ne_zero_of_congruence_posDef (P Q S : Sym2)
    (hQ : Q.PosDef) (hcong : Q = S.transpose * P * S) :
    S.det ≠ 0 := by
  have hdet : Q.det ≠ 0 :=
    (Q.isUnit_iff_isUnit_det.mp hQ.isUnit).ne_zero
  rw [hcong, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
  intro hS
  simp [hS] at hdet

theorem sum_congruence {n : ℕ} (A : Fin n → Sym2) (S : Sym2) :
    (∑ i, S.transpose * A i * S) =
      S.transpose * (∑ i, A i) * S := by
  simp [Matrix.mul_sum, Matrix.sum_mul]

/-- A limiting row congruence into any rank-three PSD factorization has
nonzero determinant. This is the invertibility step for orbit closedness. -/
theorem congruence_det_nonzero_of_rank_three {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A At : Fin p → Sym2) (Bt : Fin q → Sym2)
    (hrank : M.rank = 3)
    (halt : Factorization M At Bt)
    (S : Sym2) (hrows : ∀ i, At i = S.transpose * A i * S) :
    S.det ≠ 0 := by
  have hQ := sum_rows_posDef M At Bt halt hrank
  have hcong : (∑ i, At i) =
      S.transpose * (∑ i, A i) * S := by
    simp_rw [hrows]
    exact sum_congruence A S
  exact det_ne_zero_of_congruence_posDef _ _ _ hQ hcong

end NLA.Proofs.PF05.PositiveTopology
