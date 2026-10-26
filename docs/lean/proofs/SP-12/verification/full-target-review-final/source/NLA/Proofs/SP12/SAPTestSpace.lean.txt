import NLA.Statements.SP12
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic

/-!
# The fixed graph test space for the strong Arnold property

For a fixed graph, admissible symmetric test matrices have zero diagonal
and vanish on its edges. Injectivity of left multiplication on this actual
finite-dimensional subspace is open in the multiplying matrix. Exact pattern
identifies this condition with the original strong Arnold property.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped Matrix.Norms.Elementwise

namespace NLA.Proofs.SP12

variable {n : ℕ}

/-- The actual symmetric, zero-diagonal, off-nonedge-supported matrices. -/
def sapTestSpace (G : SimpleGraph (Fin n)) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {X | (∀ i j, X i j = X j i) ∧
    (∀ i, X i i = 0) ∧ ∀ i j, G.Adj i j → X i j = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    exact ⟨fun i j => by simp only [Matrix.add_apply, hX.1 i j, hY.1 i j],
      fun i => by simp [hX.2.1 i, hY.2.1 i],
      fun i j hij => by simp [hX.2.2 i j hij, hY.2.2 i j hij]⟩
  smul_mem' := by
    intro r X hX
    exact ⟨fun i j => by simp only [Matrix.smul_apply, smul_eq_mul, hX.1 i j],
      fun i => by simp [hX.2.1 i],
      fun i j hij => by simp [hX.2.2 i j hij]⟩

@[simp] theorem mem_sapTestSpace (G : SimpleGraph (Fin n))
    (X : Matrix (Fin n) (Fin n) ℝ) :
    X ∈ sapTestSpace G ↔ (∀ i j, X i j = X j i) ∧
      (∀ i, X i i = 0) ∧ ∀ i j, G.Adj i j → X i j = 0 := Iff.rfl

/-- Left multiplication on the fixed graph test space. -/
noncomputable def testMultiplication (G : SimpleGraph (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) :
    sapTestSpace G →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ({ toFun := fun X => A * X.val
     map_add' := fun X Y => by simp [Matrix.mul_add]
     map_smul' := fun r X => by simp } :
    sapTestSpace G →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ).toContinuousLinearMap

@[simp] theorem testMultiplication_apply (G : SimpleGraph (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) (X : sapTestSpace G) :
    testMultiplication G A X = A * X.val := rfl

/-- Dependence on the multiplying matrix is itself finite-dimensional linear. -/
noncomputable def testMultiplicationFamily (G : SimpleGraph (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ]
      (sapTestSpace G →L[ℝ] Matrix (Fin n) (Fin n) ℝ) where
  toFun := testMultiplication G
  map_add' := by
    intro A B
    ext X i j
    simp [Matrix.add_mul]
  map_smul' := by
    intro r A
    ext X i j
    simp

/-- The graph-supported multiplication-injectivity condition is open, even
at matrices whose pattern need not equal the graph's exact pattern. -/
theorem isOpen_injective_testMultiplication (G : SimpleGraph (Fin n)) :
    IsOpen {A : Matrix (Fin n) (Fin n) ℝ |
      Function.Injective (testMultiplication G A)} := by
  have hc := LinearMap.continuous_of_finiteDimensional (𝕜 := ℝ)
    (E := Matrix (Fin n) (Fin n) ℝ)
    (F' := sapTestSpace G →L[ℝ] Matrix (Fin n) (Fin n) ℝ) (testMultiplicationFamily G)
  change Continuous (testMultiplication G) at hc
  exact (ContinuousLinearMap.isOpen_injective (𝕜 := ℝ)
    (E := sapTestSpace G) (F := Matrix (Fin n) (Fin n) ℝ)).preimage hc

/-- For an exact-pattern matrix, the fixed test-space condition is precisely
the original three-equation strong Arnold property. -/
theorem strongArnold_iff_injective_testMultiplication (G : SimpleGraph (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : NLA.Statements.SP12.HasPattern G A) :
    NLA.Statements.SP12.StrongArnold A ↔
      Function.Injective (testMultiplication G A) := by
  constructor
  · intro hs
    have key (X : sapTestSpace G) (hX : A * X.val = 0) : X = 0 := by
      apply Subtype.ext
      apply hs X.val X.property.1 hX
      · intro i j
        by_cases hij : i = j
        · subst j
          simp [X.property.2.1 i]
        · by_cases hadj : G.Adj i j
          · simp [X.property.2.2 i j hadj]
          · have hz : A i j = 0 := not_ne_iff.mp (fun hn => hadj ((hA.2 i j hij).mp hn))
            simp [hz]
      · exact X.property.2.1
    intro X Y hXY
    apply sub_eq_zero.mp
    apply key
    change testMultiplication G A (X - Y) = 0
    rw [map_sub, hXY, sub_self]
  · intro hi X hsym hmul hentry hdiag
    have hmem : X ∈ sapTestSpace G := by
      refine ⟨hsym, hdiag, ?_⟩
      intro i j hadj
      have hij : i ≠ j := G.ne_of_adj hadj
      exact (mul_eq_zero.mp (hentry i j)).resolve_left ((hA.2 i j hij).mpr hadj)
    have hx : (⟨X, hmem⟩ : sapTestSpace G) = 0 := hi (by simpa using hmul)
    exact congrArg Subtype.val hx

#assert_trust kernel isOpen_injective_testMultiplication
#assert_trust kernel strongArnold_iff_injective_testMultiplication
#print axioms isOpen_injective_testMultiplication
#print axioms strongArnold_iff_injective_testMultiplication

end NLA.Proofs.SP12
