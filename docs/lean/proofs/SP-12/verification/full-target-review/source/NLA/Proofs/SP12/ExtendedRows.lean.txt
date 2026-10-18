import NLA.Proofs.SP12.SAPTestSpace
import NLA.Proofs.SP11.GramBridge

/-!
# The actual one-vertex Gram extension and its base point

The new row is the first coordinate vector. Each old row receives one new
coordinate. At zero new coordinates the fixed graph test-space multiplication
is injective, using SAP of the old Gram matrix. Openness will preserve it
under the later small perturbation.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix.Norms.Elementwise

namespace NLA.Proofs.SP12

variable {h d : ℕ}

def extendedRows (R : Matrix (Fin h) (Fin d) ℝ) (b : Fin h → ℝ) :
    Matrix (Fin (h + 1)) (Fin (d + 1)) ℝ :=
  Fin.cons (Fin.cons 1 (fun _ => 0)) (fun i => Fin.cons (b i) (R i))

@[simp] theorem gram_extendedRows_zero_zero (R : Matrix (Fin h) (Fin d) ℝ) (b : Fin h → ℝ) :
    SP11.gram (extendedRows R b) 0 0 = 1 := by
  change (∑ k : Fin (d + 1), extendedRows R b 0 k * extendedRows R b 0 k) = 1
  simp [extendedRows, Fin.sum_univ_succ]

@[simp] theorem gram_extendedRows_zero_succ (R : Matrix (Fin h) (Fin d) ℝ) (b : Fin h → ℝ)
    (i : Fin h) : SP11.gram (extendedRows R b) 0 i.succ = b i := by
  change (∑ k : Fin (d + 1), extendedRows R b 0 k * extendedRows R b i.succ k) = b i
  simp [extendedRows, Fin.sum_univ_succ]

@[simp] theorem gram_extendedRows_succ_zero (R : Matrix (Fin h) (Fin d) ℝ) (b : Fin h → ℝ)
    (i : Fin h) : SP11.gram (extendedRows R b) i.succ 0 = b i := by
  change (∑ k : Fin (d + 1), extendedRows R b i.succ k * extendedRows R b 0 k) = b i
  simp [extendedRows, Fin.sum_univ_succ]

@[simp] theorem gram_extendedRows_succ_succ (R : Matrix (Fin h) (Fin d) ℝ) (b : Fin h → ℝ)
    (i j : Fin h) :
    SP11.gram (extendedRows R b) i.succ j.succ = b i * b j + SP11.gram R i j := by
  change (∑ k : Fin (d + 1), extendedRows R b i.succ k * extendedRows R b j.succ k) =
    b i * b j + ∑ k, R i k * R j k
  simp [extendedRows, Fin.sum_univ_succ]

/-- All entries of the actual extended Gram matrix depend continuously on the
old rows and added coordinates, using their ordinary finite product topology. -/
theorem continuous_gram_extendedRows :
    Continuous (fun p : Matrix (Fin h) (Fin d) ℝ × (Fin h → ℝ) =>
      SP11.gram (extendedRows p.1 p.2)) := by
  have hrows (i : Fin (h + 1)) (k : Fin (d + 1)) :
      Continuous (fun p : Matrix (Fin h) (Fin d) ℝ × (Fin h → ℝ) =>
        extendedRows p.1 p.2 i k) := by
    cases i using Fin.cases with
    | zero =>
      cases k using Fin.cases with
      | zero => exact continuous_const
      | succ k => exact continuous_const
    | succ i =>
      cases k using Fin.cases with
      | zero => simpa only [extendedRows, Fin.cons_succ, Fin.cons_zero]
          using (show Continuous (fun p : Matrix (Fin h) (Fin d) ℝ × (Fin h → ℝ) => p.2 i) by fun_prop)
      | succ k => simpa only [extendedRows, Fin.cons_succ]
          using (show Continuous (fun p : Matrix (Fin h) (Fin d) ℝ × (Fin h → ℝ) => p.1 i k) by fun_prop)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun p : Matrix (Fin h) (Fin d) ℝ × (Fin h → ℝ) =>
    ∑ k : Fin (d + 1), extendedRows p.1 p.2 i k * extendedRows p.1 p.2 j k)
  exact continuous_finsetSum _ (fun k _ => (hrows i k).mul (hrows j k))

/-- The block-diagonal base point is injective on the fixed larger graph test
space, even though the new graph's edges have not yet been made nonzero. -/
theorem injective_testMultiplication_extendedRows_zero
    (G : SimpleGraph (Fin (h + 1))) (R : Matrix (Fin h) (Fin d) ℝ)
    (hpat : NLA.Statements.SP12.HasPattern (G.comap Fin.succ) (SP11.gram R))
    (hsap : NLA.Statements.SP12.StrongArnold (SP11.gram R)) :
    Function.Injective (testMultiplication G (SP11.gram (extendedRows R 0))) := by
  have hold := (strongArnold_iff_injective_testMultiplication
    (G.comap Fin.succ) (SP11.gram R) hpat).mp hsap
  have kernel (X : sapTestSpace G)
      (hX : SP11.gram (extendedRows R 0) * X.val = 0) : X = 0 := by
    have hfirst (j : Fin (h + 1)) : X.val 0 j = 0 := by
      have hz := congrFun (congrFun hX 0) j
      simpa only [Matrix.mul_apply, Fin.sum_univ_succ, gram_extendedRows_zero_zero,
        gram_extendedRows_zero_succ, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
        add_zero, one_mul, Matrix.zero_apply] using hz
    let Y : sapTestSpace (G.comap Fin.succ) :=
      ⟨X.val.submatrix Fin.succ Fin.succ,
        (fun i j => X.property.1 i.succ j.succ), (fun i => X.property.2.1 i.succ),
        fun i j hij => X.property.2.2 i.succ j.succ hij⟩
    have hmul : SP11.gram R * Y.val = 0 := by
      ext i j
      have hz := congrFun (congrFun hX i.succ) j.succ
      simpa only [Matrix.mul_apply, Fin.sum_univ_succ, gram_extendedRows_succ_zero,
        gram_extendedRows_succ_succ, Pi.zero_apply, zero_mul, zero_add,
        Matrix.zero_apply, Y, Matrix.submatrix_apply] using hz
    have hy : Y = 0 := hold (by simpa only [testMultiplication_apply, map_zero] using hmul)
    apply Subtype.ext
    ext i j
    cases i using Fin.cases with
    | zero => exact hfirst j
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (X.property.1 _ _).trans (hfirst i.succ)
      | succ j => exact congrFun (congrFun (congrArg Subtype.val hy) i) j
  intro X Y hXY
  apply sub_eq_zero.mp
  apply kernel
  change testMultiplication G (SP11.gram (extendedRows R 0)) (X - Y) = 0
  rw [map_sub, hXY, sub_self]

#assert_trust kernel continuous_gram_extendedRows
#assert_trust kernel injective_testMultiplication_extendedRows_zero
#print axioms injective_testMultiplication_extendedRows_zero

end NLA.Proofs.SP12
