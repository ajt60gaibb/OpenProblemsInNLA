import NLA.Proofs.PF05.ContactQuartic
import NLA.Proofs.PF05.PositiveReduction

/-! Actual singular factors as finite affine contact nodes, with exact signs. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
open NLA.Statements.PF05 CoordinateActions Polynomial
noncomputable section

def primalSlope (A : M2) : ℝ := A 0 1 / A 0 0
def dualSlope (B : M2) : ℝ := -B 0 1 / B 1 1

theorem singular_primal_chart (A : M2) (hA : Symmetric A)
    (ha : 0 < A 0 0) (hd : A.det=0) :
    A = A 0 0 • chartOuter (primalSlope A) := by
  have hd' : A 0 0 * A 1 1 - A 0 1 ^ 2 = 0 := by
    simpa [Matrix.det_fin_two, hA 1 0, pow_two] using hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartOuter, primalSlope, Matrix.smul_apply, smul_eq_mul, hA 1 0] <;>
    field_simp [ne_of_gt ha] <;> nlinarith [hd']

theorem singular_dual_chart (B : M2) (hB : Symmetric B)
    (hb : 0 < B 1 1) (hd : B.det=0) :
    B = B 1 1 • chartDual (dualSlope B) := by
  have hd' : B 0 0 * B 1 1 - B 0 1 ^ 2 = 0 := by
    simpa [Matrix.det_fin_two, hB 1 0, pow_two] using hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartDual, dualSlope, Matrix.smul_apply, smul_eq_mul, hB 1 0] <;>
    field_simp [ne_of_gt hb] <;> nlinarith [hd']

theorem coordinateActions_trace_pairing (L : M3) (A B : M2)
    (hA : Symmetric A) (hB : Symmetric B) :
    Matrix.trace (primal L A * B) = Matrix.trace (A * dual L B) := by
  have h := coordinateActions_trace_cancel L A B hA hB
  simp only [Matrix.mul_neg, Matrix.trace_neg] at h
  linarith

/-- The dual action is forced by actual rank-three factorization data. -/
theorem actual_dual_identity_of_primal {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A At : Fin p → M2) (B Bt : Fin q → M2)
    (hf : Factorization M A B) (hft : Factorization M At Bt) (hrank : M.rank=3)
    (L : M3) (hAt : ∀ i, At i=primal L (A i)) :
    ∀ j, dual L (Bt j)=B j := by
  intro j
  have hs : Symmetric (dual L (Bt j)-B j) := by
    intro a b
    simp [dual_symmetric L (Bt j) a b, (hf.2.1 j).1 a b]
  have hz := trace_pairing_left_nondegenerate_of_rank_three M A B hf hrank
    (dual L (Bt j)-B j) hs (by
      intro i
      rw [Matrix.mul_sub, Matrix.trace_sub,
        ← coordinateActions_trace_pairing L (A i) (Bt j) (hf.1 i).1 (hft.2.1 j).1,
        ← hAt i, ← hft.2.2 i j, ← hf.2.2 i j]
      ring)
  exact sub_eq_zero.mp hz

/-- All singular primal and dual contacts retain their original vertex indices. -/
def ContactIndex {p q : ℕ} (A : Fin p → M2) (B : Fin q → M2) :=
  {i : Fin p // (A i).det=0} ⊕ {j : Fin q // (B j).det=0}

def contactNode {p q : ℕ} (A : Fin p → M2) (B : Fin q → M2) : ContactIndex A B → ℝ
  | .inl i => primalSlope (A i)
  | .inr j => dualSlope (B j)

def contactSign {p q : ℕ} (A : Fin p → M2) (B : Fin q → M2) : ContactIndex A B → ℝ
  | .inl _ => 1
  | .inr _ => -1

theorem contactSign_ne_zero {p q : ℕ} (A : Fin p → M2) (B : Fin q → M2)
    (i : ContactIndex A B) : contactSign A B i ≠ 0 := by cases i <;> norm_num [contactSign]

theorem chart_trace_same (t : ℝ) : Matrix.trace (chartOuter t * chartDual t)=0 := by
  simp [chartOuter, chartDual, Matrix.trace_fin_two]
  ring

/-- Distinct positive rays and strict positivity of actual entries give distinct
nodes on both sides, including the cross-side contact exclusion. -/
theorem contactNode_injective {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → M2) (B : Fin q → M2) (hf : Factorization M A B)
    (hpos : ∀ i j, 0 < M i j) (ha : ∀ i, 0 < A i 0 0) (hb : ∀ j, 0 < B j 1 1)
    (hda : ∀ i k, SamePositiveRay (A i) (A k) → i=k)
    (hdb : ∀ j k, SamePositiveRay (B j) (B k) → j=k) :
    Function.Injective (contactNode A B) := by
  have hcross (i : {i : Fin p // (A i).det=0}) (j : {j : Fin q // (B j).det=0}) :
      primalSlope (A i) ≠ dualSlope (B j) := by
    intro h
    have hi := singular_primal_chart (A i) (hf.1 i).1 (ha i) i.property
    have hj := singular_dual_chart (B j) (hf.2.1 j).1 (hb j) j.property
    have hp := hpos i j
    rw [hf.2.2, hi, hj, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
      Matrix.trace_smul, h, chart_trace_same] at hp
    simp at hp
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl k =>
      congr 1
      apply Subtype.ext
      apply hda
      refine ⟨A i 0 0 / A k 0 0, div_pos (ha i) (ha k), ?_⟩
      change primalSlope (A i)=primalSlope (A k) at hxy
      calc
        A i = A i 0 0 • chartOuter (primalSlope (A i)) :=
          singular_primal_chart (A i) (hf.1 i).1 (ha i) i.property
        _ = (A i 0 0 / A k 0 0) • A k := by
          conv_rhs => arg 2; rw [singular_primal_chart (A k) (hf.1 k).1 (ha k) k.property]
          rw [hxy, smul_smul, div_mul_cancel₀ _ (ne_of_gt (ha k))]
    | inr j => exact (hcross i j hxy).elim
  | inr j =>
    cases y with
    | inl i => exact (hcross i j hxy.symm).elim
    | inr k =>
      congr 1
      apply Subtype.ext
      apply hdb
      refine ⟨B j 1 1 / B k 1 1, div_pos (hb j) (hb k), ?_⟩
      change dualSlope (B j)=dualSlope (B k) at hxy
      calc
        B j = B j 1 1 • chartDual (dualSlope (B j)) :=
          singular_dual_chart (B j) (hf.2.1 j).1 (hb j) j.property
        _ = (B j 1 1 / B k 1 1) • B k := by
          conv_rhs => arg 2; rw [singular_dual_chart (B k) (hf.2.1 k).1 (hb k) k.property]
          rw [hxy, smul_smul, div_mul_cancel₀ _ (ne_of_gt (hb k))]

#assert_trust kernel singular_primal_chart
#assert_trust kernel singular_dual_chart
#assert_trust kernel actual_dual_identity_of_primal
#assert_trust kernel contactNode_injective
#print axioms actual_dual_identity_of_primal
#print axioms contactNode_injective
end
end NLA.Proofs.PF05
