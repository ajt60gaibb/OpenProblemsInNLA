import NLA.Proofs.PF05.Basic

/-! Full-rank coordinate change between two PSD factorizations of the same rank-three matrix.
The 3×3 operator is invertible and acts dually on the two factor families. -/
set_option autoImplicit false
namespace NLA.Proofs.PF05
open NLA.Statements.PF05

theorem left_inverse_of_row_span {p : ℕ}
    (X : Matrix (Fin p) (Fin 3) ℝ)
    (hspan : Submodule.span ℝ (Set.range X.row) = ⊤) :
    ∃ U : Matrix (Fin 3) (Fin p) ℝ, U * X = 1 := by
  have hsurj : Function.Surjective X.vecMul := by
    rw [← Matrix.coe_vecMulLinear]
    apply LinearMap.range_eq_top.mp
    rw [range_vecMulLinear]
    exact hspan
  exact Matrix.vecMul_surjective_iff_exists_left_inverse.mp hsurj

theorem right_inverse_of_column_span {q : ℕ}
    (Y : Matrix (Fin 3) (Fin q) ℝ)
    (hspan : Submodule.span ℝ (Set.range Y.col) = ⊤) :
    ∃ V : Matrix (Fin q) (Fin 3) ℝ, Y * V = 1 := by
  have hsurj : Function.Surjective Y.mulVec := by
    rw [← Matrix.coe_mulVecLin]
    apply LinearMap.range_eq_top.mp
    rw [Matrix.range_mulVecLin]
    exact hspan
  exact Matrix.mulVec_surjective_iff_exists_right_inverse.mp hsurj

theorem full_rank_factorization_change_of_basis {p q : ℕ}
    (X Xt : Matrix (Fin p) (Fin 3) ℝ)
    (Y Yt : Matrix (Fin 3) (Fin q) ℝ)
    (hprod : X * Y = Xt * Yt)
    (hXspan : Submodule.span ℝ (Set.range X.row) = ⊤)
    (hXtspan : Submodule.span ℝ (Set.range Xt.row) = ⊤)
    (hYspan : Submodule.span ℝ (Set.range Y.col) = ⊤)
    (hYtspan : Submodule.span ℝ (Set.range Yt.col) = ⊤) :
    ∃ L K : Matrix (Fin 3) (Fin 3) ℝ,
      L * K = 1 ∧ K * L = 1 ∧ Xt = X * L ∧ Yt = K * Y := by
  obtain ⟨U, hUX⟩ := left_inverse_of_row_span X hXspan
  obtain ⟨Ut, hUtXt⟩ := left_inverse_of_row_span Xt hXtspan
  obtain ⟨V, hYV⟩ := right_inverse_of_column_span Y hYspan
  obtain ⟨Vt, hYtVt⟩ := right_inverse_of_column_span Yt hYtspan
  let L := Y * Vt
  let K := Yt * V
  have hXt : Xt = X * L := by
    calc
      Xt = Xt * (Yt * Vt) := by rw [hYtVt]; simp
      _ = (Xt * Yt) * Vt := by simp [Matrix.mul_assoc]
      _ = (X * Y) * Vt := by rw [hprod]
      _ = X * L := by simp [L, Matrix.mul_assoc]
  have hX : X = Xt * K := by
    calc
      X = X * (Y * V) := by rw [hYV]; simp
      _ = (X * Y) * V := by simp [Matrix.mul_assoc]
      _ = (Xt * Yt) * V := by rw [hprod]
      _ = Xt * K := by simp [K, Matrix.mul_assoc]
  have hLK : L * K = 1 := by
    calc
      L * K = (U * X) * (L * K) := by rw [hUX]; simp
      _ = U * ((X * L) * K) := by simp [Matrix.mul_assoc]
      _ = U * (Xt * K) := by rw [hXt]
      _ = U * X := by rw [← hX]
      _ = 1 := hUX
  have hKL : K * L = 1 := by
    calc
      K * L = (Ut * Xt) * (K * L) := by rw [hUtXt]; simp
      _ = Ut * ((Xt * K) * L) := by simp [Matrix.mul_assoc]
      _ = Ut * (X * L) := by rw [hX]
      _ = Ut * Xt := by rw [← hXt]
      _ = 1 := hUtXt
  have hY : Y = L * Yt := by
    calc
      Y = (U * X) * Y := by rw [hUX]; simp
      _ = U * (X * Y) := by simp [Matrix.mul_assoc]
      _ = U * (Xt * Yt) := by rw [hprod]
      _ = U * ((X * L) * Yt) := by rw [← hXt]
      _ = (U * X) * (L * Yt) := by simp [Matrix.mul_assoc]
      _ = L * Yt := by rw [hUX]; simp
  have hYt : Yt = K * Y := by
    calc
      Yt = (K * L) * Yt := by rw [hKL]; simp
      _ = K * (L * Yt) := by simp [Matrix.mul_assoc]
      _ = K * Y := by rw [← hY]
  exact ⟨L, K, hLK, hKL, hXt, hYt⟩

theorem factorization_change_of_basis {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A At : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B Bt : Fin q → Matrix (Fin 2) (Fin 2) ℝ)
    (h : Factorization M A B) (ht : Factorization M At Bt)
    (hrank : M.rank = 3) :
    ∃ L : Matrix (Fin 3) (Fin 3) ℝ,
      L.det ≠ 0 ∧
      leftCoordinates At = leftCoordinates A * L ∧
      rightCoordinates Bt = L⁻¹ * rightCoordinates B := by
  have hprod : leftCoordinates A * rightCoordinates B =
      leftCoordinates At * rightCoordinates Bt := by
    rw [← factorization_coordinates M A B h, ← factorization_coordinates M At Bt ht]
  obtain ⟨L, K, hLK, _hKL, hleft, hright⟩ :=
    full_rank_factorization_change_of_basis
      (leftCoordinates A) (leftCoordinates At)
      (rightCoordinates B) (rightCoordinates Bt) hprod
      (factorization_coordinate_spans M A B h hrank).1
      (factorization_coordinate_spans M At Bt ht hrank).1
      (factorization_coordinate_spans M A B h hrank).2
      (factorization_coordinate_spans M At Bt ht hrank).2
  have hdet : L.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse hLK
  have hinv : L⁻¹ = K := Matrix.inv_eq_right_inv hLK
  exact ⟨L, hdet, hleft, by rwa [hinv]⟩

end NLA.Proofs.PF05
