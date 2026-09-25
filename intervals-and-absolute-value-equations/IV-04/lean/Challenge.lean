import Mathlib
import Reduction

namespace IV04

structure RationalInterval where
  lo : ℚ
  hi : ℚ
  h : lo ≤ hi

structure Input where
  n : ℕ
  hn : 1 ≤ n
  matrixEntry : Fin n → Fin n → RationalInterval
  rhsEntry : Fin n → RationalInterval

def intervalMem (J : RationalInterval) (x : ℝ) : Prop :=
  (J.lo : ℝ) ≤ x ∧ x ≤ (J.hi : ℝ)

def tridiagonal (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, i.val + 1 < j.val ∨ j.val + 1 < i.val → A i j = 0

def matrixAdmissible (I : Input) (A : Matrix (Fin I.n) (Fin I.n) ℝ) : Prop :=
  tridiagonal I.n A ∧
  (∀ i, intervalMem (I.matrixEntry i i) (A i i)) ∧
  (∀ i j, i.val + 1 = j.val →
    intervalMem (I.matrixEntry i j) (A i j)) ∧
  (∀ i j, j.val + 1 = i.val →
    intervalMem (I.matrixEntry i j) (A i j))

def rhsAdmissible (I : Input) (b : Fin I.n → ℝ) : Prop :=
  ∀ i, intervalMem (I.rhsEntry i) (b i)

def unitedSolutionSet (I : Input) : Set (Fin I.n → ℝ) :=
  {x | ∃ A : Matrix (Fin I.n) (Fin I.n) ℝ, ∃ b : Fin I.n → ℝ,
    matrixAdmissible I A ∧ rhsAdmissible I b ∧ A.mulVec x = b}

def coordinateValues (I : Input) (i : Fin I.n) : Set ℝ :=
  (fun x : Fin I.n → ℝ => x i) '' unitedSolutionSet I

inductive HullCase (S : Set ℝ) : Prop where
  | empty (h : S = ∅)
  | bounded (lo hi : ℚ) (hlo : lo ≤ hi) (h : S = Set.Icc (lo : ℝ) (hi : ℝ))
  | lowerUnbounded (hi : ℚ) (h : S = Set.Iic (hi : ℝ))
  | upperUnbounded (lo : ℚ) (h : S = Set.Ici (lo : ℝ))
  | all (h : S = Set.univ)

def unitedSolutionHull (I : Input) : Prop :=
  ∀ i : Fin I.n, HullCase (coordinateValues I i)

def IV04Statement : Prop :=
  ∀ I : Input, unitedSolutionHull I

theorem corner_solution_verified (M : TwoByTwo) (x₁ x₂ : ℚ)
    (hb : M.b = 1) (hdet : det M ≠ 0)
    (h₁ : M.a * x₁ + M.b * x₂ = 0)
    (h₂ : M.c * x₁ + M.d * x₂ = -1) :
    x₁ = 1 / det M :=
  corner_solution M x₁ x₂ hb hdet h₁ h₂

#check IV04Statement

end IV04
