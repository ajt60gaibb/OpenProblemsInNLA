import NLA.Statements.PF05
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-! Elementary two-by-two matrix facts used by the PF-05 proof.
These lemmas do not establish the full rigidity equivalence. -/
set_option autoImplicit false
namespace NLA.Proofs.PF05
open NLA.Statements.PF05

/-- Identify the frozen statement's quadratic-form PSD predicate with Mathlib PSD. -/
theorem psd_iff_posSemidef {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) :
    PositiveSemidefinite A ↔ Matrix.PosSemidef A := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  simp only [PositiveSemidefinite, NLA.Statements.PF05.Symmetric]
  constructor
  · rintro ⟨hs, hp⟩
    constructor
    · rw [Matrix.isHermitian_iff_isSymm]
      exact Matrix.IsSymm.ext fun i j => (hs j i)
    · intro x
      simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc] using hp x
  · rintro ⟨hs, hp⟩
    constructor
    · have hs' := (Matrix.isHermitian_iff_isSymm.mp hs)
      intro i j
      exact hs'.apply j i
    · intro x
      simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc] using hp x

theorem psd_diag_nonneg {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : PositiveSemidefinite A) (i : Fin k) : 0 ≤ A i i :=
  (psd_iff_posSemidef A).mp hA |>.diag_nonneg

theorem psd_det_nonneg {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : PositiveSemidefinite A) : 0 ≤ A.det :=
  ((psd_iff_posSemidef A).mp hA).det_nonneg

theorem psd_zero_of_trace_zero {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : PositiveSemidefinite A) (htrace : A.trace = 0) : A = 0 :=
  (((psd_iff_posSemidef A).mp hA).trace_eq_zero_iff).mp htrace

private theorem trace_pair_P (C : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.trace (C * !![1,0;0,0]) = C 0 0 := by
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

private theorem trace_pair_Q (C : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.trace (C * !![0,0;0,1]) = C 1 1 := by
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

private theorem trace_pair_R (C : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.trace (C * !![0,1;1,0]) = C 0 1 + C 1 0 := by
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- The trace pairing is nondegenerate on the real symmetric two-by-two space. -/
theorem trace_pairing_symm_nondegenerate
    (C : Matrix (Fin 2) (Fin 2) ℝ)
    (hC : NLA.Statements.PF05.Symmetric C)
    (h : ∀ B : Matrix (Fin 2) (Fin 2) ℝ,
      NLA.Statements.PF05.Symmetric B → Matrix.trace (C * B) = 0) :
    C = 0 := by
  have hP : NLA.Statements.PF05.Symmetric (!![1,0;0,0] : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro i j; fin_cases i <;> fin_cases j <;> simp
  have hQ : NLA.Statements.PF05.Symmetric (!![0,0;0,1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro i j; fin_cases i <;> fin_cases j <;> simp
  have hR : NLA.Statements.PF05.Symmetric (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro i j; fin_cases i <;> fin_cases j <;> simp
  have h00 : C 0 0 = 0 := by simpa [trace_pair_P] using h _ hP
  have h11 : C 1 1 = 0 := by simpa [trace_pair_Q] using h _ hQ
  have hsum : C 0 1 + C 1 0 = 0 := by simpa [trace_pair_R] using h _ hR
  have h01 : C 0 1 = 0 := by rw [← hC 0 1] at hsum; linarith
  have h10 : C 1 0 = 0 := by rw [hC 1 0]; exact h01
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h01, h10]

private theorem quadratic_form_fin_two
    (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : NLA.Statements.PF05.Symmetric A) (x : Fin 2 → ℝ) :
    (∑ i, ∑ j, x i * A i j * x j) =
      A 0 0 * (x 0)^2 + 2 * A 0 1 * x 0 * x 1 + A 1 1 * (x 1)^2 := by
  simp only [Fin.sum_univ_two]
  rw [hA 1 0]
  ring

/-- The exact two-by-two PSD criterion used for straight-line feasibility. -/
theorem psd_fin_two_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    PositiveSemidefinite A ↔
      NLA.Statements.PF05.Symmetric A ∧
      0 ≤ A 0 0 ∧ 0 ≤ A 1 1 ∧ 0 ≤ A.det := by
  constructor
  · intro hA
    exact ⟨hA.1, psd_diag_nonneg A hA 0, psd_diag_nonneg A hA 1,
      psd_det_nonneg A hA⟩
  · rintro ⟨hs, ha, hc, hdet⟩
    refine ⟨hs, ?_⟩
    intro x
    rw [quadratic_form_fin_two A hs x]
    have hdet' : 0 ≤ A 0 0 * A 1 1 - (A 0 1)^2 := by
      simpa [Matrix.det_fin_two, hs 1 0, sq] using hdet
    rcases eq_or_lt_of_le ha with hzero | hpos
    · have hb : A 0 1 = 0 := by nlinarith [sq_nonneg (A 0 1)]
      rw [← hzero, hb]
      nlinarith [sq_nonneg (x 1), mul_nonneg hc (sq_nonneg (x 1))]
    · by_contra! hq
      have hmul : A 0 0 *
          (A 0 0 * (x 0)^2 + 2 * A 0 1 * x 0 * x 1 + A 1 1 * (x 1)^2) < 0 :=
        mul_neg_of_pos_of_neg hpos hq
      nlinarith [sq_nonneg (A 0 0 * x 0 + A 0 1 * x 1),
        mul_nonneg hdet' (sq_nonneg (x 1))]

/-! Zero-diagonal and normalized zero-pair consequences. -/
theorem psd_zero_00_offdiag (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : PositiveSemidefinite A) (h00 : A 0 0 = 0) :
    A 0 1 = 0 ∧ A 1 0 = 0 := by
  have hdet := psd_det_nonneg A hA
  have h01 : A 0 1 = 0 := by
    rw [Matrix.det_fin_two, hA.1 1 0, h00] at hdet
    nlinarith [sq_nonneg (A 0 1)]
  exact ⟨h01, by rw [hA.1 1 0]; exact h01⟩

theorem psd_zero_11_offdiag (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : PositiveSemidefinite A) (h11 : A 1 1 = 0) :
    A 0 1 = 0 ∧ A 1 0 = 0 := by
  have hdet := psd_det_nonneg A hA
  have h01 : A 0 1 = 0 := by
    rw [Matrix.det_fin_two, hA.1 1 0, h11] at hdet
    nlinarith [sq_nonneg (A 0 1)]
  exact ⟨h01, by rw [hA.1 1 0]; exact h01⟩

theorem trace_zero_with_P
    (a : ℝ) (ha : 0 < a) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : PositiveSemidefinite B)
    (htrace : Matrix.trace ((!![a,0;0,0] : Matrix (Fin 2) (Fin 2) ℝ) * B) = 0) :
    B = !![0,0;0,B 1 1] := by
  have hmul : a * B 0 0 = 0 := by
    simpa [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using htrace
  have h00 : B 0 0 = 0 := (mul_eq_zero.mp hmul).resolve_left (ne_of_gt ha)
  obtain ⟨h01, h10⟩ := psd_zero_00_offdiag B hB h00
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10]

theorem trace_zero_with_Q
    (b : ℝ) (hb : 0 < b) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : PositiveSemidefinite A)
    (htrace : Matrix.trace (A * (!![0,0;0,b] : Matrix (Fin 2) (Fin 2) ℝ)) = 0) :
    A = !![A 0 0,0;0,0] := by
  have hmul : A 1 1 * b = 0 := by
    simpa [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two] using htrace
  have h11 : A 1 1 = 0 := (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hb)
  obtain ⟨h01, h10⟩ := psd_zero_11_offdiag A hA h11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h11, h01, h10]

/-! Rank-three coordinate representation of a two-by-two factorization. -/
theorem trace_mul_symmetric_coordinates
    (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : NLA.Statements.PF05.Symmetric A)
    (hB : NLA.Statements.PF05.Symmetric B) :
    Matrix.trace (A * B) =
      A 0 0 * B 0 0 + A 1 1 * B 1 1 + 2 * A 0 1 * B 0 1 := by
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hA 1 0, hB 1 0]
  ring

def leftCoordinates {p : ℕ}
    (A : Fin p → Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin p) (Fin 3) ℝ :=
  fun i k => (![A i 0 0, A i 1 1, A i 0 1] : Fin 3 → ℝ) k

def rightCoordinates {q : ℕ}
    (B : Fin q → Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 3) (Fin q) ℝ :=
  fun k j => (![B j 0 0, B j 1 1, 2 * B j 0 1] : Fin 3 → ℝ) k

theorem factorization_coordinates {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B : Fin q → Matrix (Fin 2) (Fin 2) ℝ)
    (h : Factorization M A B) :
    M = leftCoordinates A * rightCoordinates B := by
  ext i j
  rw [h.2.2 i j]
  rw [trace_mul_symmetric_coordinates (A i) (B j) (h.1 i).1 (h.2.1 j).1]
  simp [leftCoordinates, rightCoordinates, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem factorization_coordinates_full_rank {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B : Fin q → Matrix (Fin 2) (Fin 2) ℝ)
    (h : Factorization M A B) (hrank : M.rank = 3) :
    (leftCoordinates A).rank = 3 ∧ (rightCoordinates B).rank = 3 := by
  rw [factorization_coordinates M A B h] at hrank
  have hL : 3 ≤ (leftCoordinates A).rank :=
    hrank.symm.le.trans (Matrix.rank_mul_le_left (leftCoordinates A) (rightCoordinates B))
  have hR : 3 ≤ (rightCoordinates B).rank :=
    hrank.symm.le.trans (Matrix.rank_mul_le_right (leftCoordinates A) (rightCoordinates B))
  exact ⟨Nat.le_antisymm (Matrix.rank_le_width _) hL,
    Nat.le_antisymm (Matrix.rank_le_height _) hR⟩

/-! Rank-three spanning and exact zero-row/column consequences. -/
theorem factorization_coordinate_spans {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B : Fin q → Matrix (Fin 2) (Fin 2) ℝ)
    (h : Factorization M A B) (hrank : M.rank = 3) :
    Submodule.span ℝ (Set.range (leftCoordinates A).row) = ⊤ ∧
    Submodule.span ℝ (Set.range (rightCoordinates B).col) = ⊤ := by
  obtain ⟨hL, hR⟩ := factorization_coordinates_full_rank M A B h hrank
  constructor
  · apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hL]
    simp
  · apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_cols, hR]
    simp

theorem dotProduct_zero_of_column_span {q : ℕ}
    (R : Matrix (Fin 3) (Fin q) ℝ)
    (hspan : Submodule.span ℝ (Set.range R.col) = ⊤)
    (v : Fin 3 → ℝ)
    (h : ∀ j, v ⬝ᵥ R.col j = 0) : v = 0 := by
  let f : (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun w => v ⬝ᵥ w
      map_add' := fun x y => dotProduct_add v x y
      map_smul' := fun a x => dotProduct_smul a v x }
  have hle : Submodule.span ℝ (Set.range R.col) ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro w ⟨j, rfl⟩
    exact h j
  have htop : (⊤ : Submodule ℝ (Fin 3 → ℝ)) ≤ LinearMap.ker f := by
    simpa [hspan] using hle
  apply dotProduct_eq_zero v
  intro w
  exact LinearMap.mem_ker.mp (htop (Submodule.mem_top))

theorem trace_pairing_right_nondegenerate_of_rank_three {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B : Fin q → Matrix (Fin 2) (Fin 2) ℝ)
    (h : Factorization M A B) (hrank : M.rank = 3)
    (C : Matrix (Fin 2) (Fin 2) ℝ)
    (hC : NLA.Statements.PF05.Symmetric C)
    (horth : ∀ j, Matrix.trace (C * B j) = 0) : C = 0 := by
  let v : Fin 3 → ℝ := ![C 0 0, C 1 1, C 0 1]
  have hcol : ∀ j, v ⬝ᵥ (rightCoordinates B).col j = 0 := by
    intro j
    have htr := trace_mul_symmetric_coordinates C (B j) hC (h.2.1 j).1
    have ht := htr.symm.trans (horth j)
    simp [v, rightCoordinates, dotProduct, Fin.sum_univ_three]
    nlinarith [ht]
  have hv : v = 0 := dotProduct_zero_of_column_span (rightCoordinates B)
    (factorization_coordinate_spans M A B h hrank).2 v hcol
  have h00 : C 0 0 = 0 := by simpa [v] using congrFun hv 0
  have h11 : C 1 1 = 0 := by simpa [v] using congrFun hv 1
  have h01 : C 0 1 = 0 := by simpa [v] using congrFun hv 2
  have h10 : C 1 0 = 0 := by rw [hC 1 0]; exact h01
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h01, h10]

theorem trace_pairing_left_nondegenerate_of_rank_three {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B : Fin q → Matrix (Fin 2) (Fin 2) ℝ)
    (h : Factorization M A B) (hrank : M.rank = 3)
    (C : Matrix (Fin 2) (Fin 2) ℝ)
    (hC : NLA.Statements.PF05.Symmetric C)
    (horth : ∀ i, Matrix.trace (A i * C) = 0) : C = 0 := by
  let v : Fin 3 → ℝ := ![C 0 0, C 1 1, 2 * C 0 1]
  have hspan : Submodule.span ℝ
      (Set.range ((leftCoordinates A).transpose).col) = ⊤ := by
    simpa [Matrix.col_transpose] using
      (factorization_coordinate_spans M A B h hrank).1
  have hcol : ∀ i, v ⬝ᵥ ((leftCoordinates A).transpose).col i = 0 := by
    intro i
    have htr := trace_mul_symmetric_coordinates (A i) C (h.1 i).1 hC
    have ht := htr.symm.trans (horth i)
    simp [v, leftCoordinates, dotProduct, Fin.sum_univ_three]
    nlinarith [ht]
  have hv : v = 0 := dotProduct_zero_of_column_span (leftCoordinates A).transpose
    hspan v hcol
  have h00 : C 0 0 = 0 := by simpa [v] using congrFun hv 0
  have h11 : C 1 1 = 0 := by simpa [v] using congrFun hv 1
  have h01 : C 0 1 = 0 := by
    have h2 := congrFun hv 2
    simp [v] at h2
    linarith
  have h10 : C 1 0 = 0 := by rw [hC 1 0]; exact h01
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h01, h10]

theorem factor_zero_row {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B : Fin q → Matrix (Fin 2) (Fin 2) ℝ)
    (h : Factorization M A B) (hrank : M.rank = 3)
    (i : Fin p) (hrow : ∀ j, M i j = 0) : A i = 0 := by
  apply trace_pairing_right_nondegenerate_of_rank_three M A B h hrank (A i) (h.1 i).1
  intro j
  exact (h.2.2 i j).symm.trans (hrow j)

theorem factor_zero_column {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B : Fin q → Matrix (Fin 2) (Fin 2) ℝ)
    (h : Factorization M A B) (hrank : M.rank = 3)
    (j : Fin q) (hcol : ∀ i, M i j = 0) : B j = 0 := by
  apply trace_pairing_left_nondegenerate_of_rank_three M A B h hrank (B j) (h.2.1 j).1
  intro i
  exact (h.2.2 i j).symm.trans (hcol i)

theorem feasible_zero_row {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A E : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B F : Fin q → Matrix (Fin 2) (Fin 2) ℝ)
    (h : Factorization M A B) (hrank : M.rank = 3)
    (hEF : FeasibleDirection A E B F)
    (i : Fin p) (hrow : ∀ j, M i j = 0) : E i = 0 := by
  have hAi := factor_zero_row M A B h hrank i hrow
  apply trace_pairing_right_nondegenerate_of_rank_three M A B h hrank (E i) (hEF.1 i)
  intro j
  have hd := hEF.2.2.1 i j
  simpa [hAi] using hd

theorem feasible_zero_column {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A E : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B F : Fin q → Matrix (Fin 2) (Fin 2) ℝ)
    (h : Factorization M A B) (hrank : M.rank = 3)
    (hEF : FeasibleDirection A E B F)
    (j : Fin q) (hcol : ∀ i, M i j = 0) : F j = 0 := by
  have hBj := factor_zero_column M A B h hrank j hcol
  apply trace_pairing_left_nondegenerate_of_rank_three M A B h hrank (F j) (hEF.2.1 j)
  intro i
  have hd := hEF.2.2.1 i j
  simpa [hBj] using hd

/-! A zero trace of two PSD factors forces their product to vanish. -/
open scoped MatrixOrder
open Matrix
theorem trace_zero_psd_mul_eq_zero {k : ℕ}
    (A B : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrace : Matrix.trace (A * B) = 0) : A * B = 0 := by
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨Y, hY⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  simp only [star_eq_conjTranspose] at hX hY
  subst A
  subst B
  have htrace' : Matrix.trace ((X * Yᴴ).conjTranspose * (X * Yᴴ)) = 0 := by
    calc
      Matrix.trace ((X * Yᴴ).conjTranspose * (X * Yᴴ))
          = Matrix.trace (Y * (Xᴴ * X * Yᴴ)) := by
              simp [Matrix.mul_assoc]
      _ = Matrix.trace ((Xᴴ * X * Yᴴ) * Y) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Xᴴ * X) * (Yᴴ * Y)) := by simp [Matrix.mul_assoc]
      _ = 0 := htrace
  have hXY : X * Yᴴ = 0 :=
    Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htrace'
  calc
    (Xᴴ * X) * (Yᴴ * Y) = Xᴴ * (X * Yᴴ) * Y := by simp [Matrix.mul_assoc]
    _ = 0 := by rw [hXY]; simp

theorem det_zero_of_mul_zero_right_nonzero {k : ℕ}
    (A B : Matrix (Fin k) (Fin k) ℝ)
    (hAB : A * B = 0) (hB : B ≠ 0) : A.det = 0 := by
  by_contra hdet
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have heq := A.nonsing_inv_mul_cancel_left B hunit
  rw [hAB] at heq
  simp at heq
  exact hB heq.symm

theorem det_zero_of_mul_zero_left_nonzero {k : ℕ}
    (A B : Matrix (Fin k) (Fin k) ℝ)
    (hAB : A * B = 0) (hA : A ≠ 0) : B.det = 0 := by
  by_contra hdet
  have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
  have heq := B.mul_nonsing_inv_cancel_right A hunit
  rw [hAB] at heq
  simp at heq
  exact hA heq.symm

/-- Zero trace of a product of two factors in the frozen PSD predicate. -/
theorem psd_trace_zero_mul_eq_zero {k : ℕ}
    (A B : Matrix (Fin k) (Fin k) ℝ)
    (hA : PositiveSemidefinite A) (hB : PositiveSemidefinite B)
    (htrace : Matrix.trace (A * B) = 0) : A * B = 0 :=
  trace_zero_psd_mul_eq_zero A B ((psd_iff_posSemidef A).mp hA)
    ((psd_iff_posSemidef B).mp hB) htrace

/-- A nonzero zero-trace PSD pair in size two consists of singular factors. -/
theorem nonzero_zero_pair_singular
    (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : PositiveSemidefinite A) (hB : PositiveSemidefinite B)
    (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (htrace : Matrix.trace (A * B) = 0) : A.det = 0 ∧ B.det = 0 := by
  have hAB := psd_trace_zero_mul_eq_zero A B hA hB htrace
  exact ⟨det_zero_of_mul_zero_right_nonzero A B hAB hB0,
    det_zero_of_mul_zero_left_nonzero A B hAB hA0⟩

end NLA.Proofs.PF05
