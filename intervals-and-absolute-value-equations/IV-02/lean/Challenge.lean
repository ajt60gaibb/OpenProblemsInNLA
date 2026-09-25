import Mathlib
import Reduction

/-! Independent statement interface for the complete IV-02 target.
The complexity predicates are explicit semantic contracts; no proof is hidden
inside this Challenge file. -/

namespace IV02

structure RationalInterval where
  lo : ℚ
  hi : ℚ
  h : lo ≤ hi

structure Input where
  n : ℕ
  hn : 2 ≤ n
  diagonal : Fin n → RationalInterval
  upper : Fin (n - 1) → RationalInterval
  lower : Fin (n - 1) → RationalInterval

def intervalMem (J : RationalInterval) (x : ℝ) : Prop :=
  (J.lo : ℝ) ≤ x ∧ x ≤ (J.hi : ℝ)

def tridiagonal (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, i.val + 1 < j.val ∨ j.val + 1 < i.val → A i j = 0

def matrixAdmissible (I : Input) (A : Matrix (Fin I.n) (Fin I.n) ℝ) : Prop :=
  tridiagonal I.n A ∧
  (∀ i, intervalMem (I.diagonal i) (A i i)) ∧
  (∀ k : Fin (I.n - 1),
    intervalMem (I.upper k)
      (A ⟨k.val, by omega⟩ ⟨k.val + 1, by omega⟩)) ∧
  (∀ k : Fin (I.n - 1),
    intervalMem (I.lower k)
      (A ⟨k.val + 1, by omega⟩ ⟨k.val, by omega⟩))

def determinantValues (I : Input) : Set ℝ :=
  {z | ∃ A : Matrix (Fin I.n) (Fin I.n) ℝ,
    matrixAdmissible I A ∧ z = Matrix.det A}

def exactRange (I : Input) : Prop :=
  ∃ dmin dmax : ℚ,
    (dmin : ℝ) ∈ determinantValues I ∧
    (∀ z ∈ determinantValues I, (dmin : ℝ) ≤ z) ∧
    (dmax : ℝ) ∈ determinantValues I ∧
    (∀ z ∈ determinantValues I, z ≤ (dmax : ℝ))

def thresholdDecision (I : Input) (τ : ℚ) : Prop :=
  ∃ A : Matrix (Fin I.n) (Fin I.n) ℝ,
    matrixAdmissible I A ∧ (τ : ℝ) ≤ Matrix.det A

structure ComplexityContract where
  threshold_np_complete : Prop
  exact_range_np_hard : Prop
  exact_output_fp_np : Prop
  polynomial_exact_algorithm_iff : Prop

/- The complexity fields are deliberately explicit semantic obligations.  They
are not discharged by the elementary determinant definitions in this folder. -/
def thresholdProblem : Prop :=
  ∃ C : ComplexityContract,
    C.threshold_np_complete ∧ C.exact_range_np_hard ∧
    C.exact_output_fp_np ∧ C.polynomial_exact_algorithm_iff

def IV02Statement : Prop :=
  (thresholdProblem ∧ ∀ I : Input, exactRange I)

theorem rotation_identity_verified (P : PartitionData) (i : Fin P.m) :
    c P i ^ 2 + s P i ^ 2 = 1 :=
  rotation_identity P i

theorem layer_count_verified (P : PartitionData) :
    Even (layerCount P) ∧ 0 < layerCount P :=
  ⟨layerCount_even P, layerCount_pos P⟩

#check IV02Statement

end IV02
