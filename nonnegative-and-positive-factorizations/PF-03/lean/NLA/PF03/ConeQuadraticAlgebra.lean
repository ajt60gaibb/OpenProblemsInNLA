import NLA.PF03.LocalQuadraticKernel

/-!
Finite bilinear sum, scalar and pullback identities used by the full C12 proof.
No numerical or positivity premise is hidden in the algebra.
Original mathematics: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance.
-/
set_option autoImplicit false
open scoped BigOperators Matrix
noncomputable section
namespace NLA.PF03

lemma cone_bilinear_eq_dotProduct {d : ℕ} (Q : RMat d d) (x y : Fin d → ℝ) :
    bilinear Q x y = x ⬝ᵥ Q.mulVec y := by
  simp only [bilinear, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

lemma cone_bilinear_symm {d : ℕ} (Q : RMat d d) (hQ : Q.IsSymm)
    (x y : Fin d → ℝ) : bilinear Q x y = bilinear Q y x := by
  have hQT : Qᵀ = Q := hQ
  rw [cone_bilinear_eq_dotProduct, cone_bilinear_eq_dotProduct]
  simpa only [hQT] using Matrix.dotProduct_transpose_mulVec Q x y

lemma cone_bilinear_sum_left {d n : ℕ} (Q : RMat d d)
    (v : Fin n → Fin d → ℝ) (y : Fin d → ℝ) :
    bilinear Q (∑ i : Fin n, v i) y = ∑ i : Fin n, bilinear Q (v i) y := by
  simp only [cone_bilinear_eq_dotProduct, sum_dotProduct]

lemma cone_bilinear_sum_right {d n : ℕ} (Q : RMat d d)
    (x : Fin d → ℝ) (v : Fin n → Fin d → ℝ) :
    bilinear Q x (∑ i : Fin n, v i) = ∑ i : Fin n, bilinear Q x (v i) := by
  simp only [cone_bilinear_eq_dotProduct, Matrix.mulVec_sum, dotProduct_sum]

lemma cone_bilinear_smul_left {d : ℕ} (Q : RMat d d)
    (t : ℝ) (x y : Fin d → ℝ) :
    bilinear Q (t • x) y = t * bilinear Q x y := by
  simp only [cone_bilinear_eq_dotProduct, smul_dotProduct, smul_eq_mul]

lemma cone_bilinear_smul_right {d : ℕ} (Q : RMat d d)
    (t : ℝ) (x y : Fin d → ℝ) :
    bilinear Q x (t • y) = t * bilinear Q x y := by
  simp only [cone_bilinear_eq_dotProduct, Matrix.mulVec_smul,
    dotProduct_smul, smul_eq_mul]

lemma cone_quad_smul {d : ℕ} (Q : RMat d d) (t : ℝ) (x : Fin d → ℝ) :
    quad Q (t • x) = (t * t) * quad Q x := by
  simp only [quad, cone_bilinear_smul_left, cone_bilinear_smul_right, mul_assoc]

lemma cone_quad_mulVec {d n : ℕ} (Q : RMat d d) (C : RMat d n)
    (z : Fin n → ℝ) :
    quad Q (C.mulVec z) = quad (Cᵀ * Q * C) z := by
  rw [quad_eq_dotProduct, quad_eq_dotProduct]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec]
  exact dotProduct_comm _ _

lemma cone_quad_sum {d n : ℕ} (Q : RMat d d) (v : Fin n → Fin d → ℝ) :
    quad Q (∑ i : Fin n, v i) =
      ∑ i : Fin n, ∑ j : Fin n, bilinear Q (v i) (v j) := by
  simp only [quad, cone_bilinear_sum_left, cone_bilinear_sum_right]
  exact Finset.sum_comm

lemma cone_double_sum_term_zero {m n : ℕ} (f : Fin m → Fin n → ℝ)
    (hnonneg : ∀ i j, 0 ≤ f i j)
    (hz : (∑ i : Fin m, ∑ j : Fin n, f i j) = 0) (i : Fin m) (j : Fin n) :
    f i j = 0 := by
  have h₁ : f i j ≤ ∑ b : Fin n, f i b :=
    Finset.single_le_sum (fun b _ => hnonneg i b) (Finset.mem_univ j)
  have h₂ : (∑ b : Fin n, f i b) ≤ ∑ a : Fin m, ∑ b : Fin n, f a b :=
    Finset.single_le_sum
      (fun a _ => Finset.sum_nonneg (fun b _ => hnonneg a b)) (Finset.mem_univ i)
  have hle := h₁.trans h₂
  rw [hz] at hle
  exact le_antisymm hle (hnonneg i j)

#print axioms cone_quad_mulVec
#assert_trust kernel cone_quad_mulVec
#print axioms cone_double_sum_term_zero
#assert_trust kernel cone_double_sum_term_zero

end NLA.PF03
