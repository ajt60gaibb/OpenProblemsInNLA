import NLA.Proofs.PF05.Operator

/-! Actual deletion of zero factors, including the empty finite core. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
namespace ZeroRestriction
open NLA.Statements.PF05
noncomputable section

abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ

/-- Retain exactly the nonzero members of a finite family. -/
structure Selection (n r : ℕ) (X : Fin n → M2) where
  pick : Fin r → Fin n
  injective : Function.Injective pick
  nonzero : ∀ a, X (pick a)≠0
  covers : ∀ i, X i≠0 → ∃ a, pick a=i

def reduced {n r : ℕ} {X : Fin n → M2} (c : Selection n r X) : Fin r → M2 := X ∘ c.pick

def lookup {n r : ℕ} {X : Fin n → M2} (c : Selection n r X) (i : Fin n) (hi : X i≠0) : Fin r :=
  Classical.choose (c.covers i hi)

theorem pick_lookup {n r : ℕ} {X : Fin n → M2}
    (c : Selection n r X) (i : Fin n) (hi : X i≠0) : c.pick (lookup c i hi)=i :=
  Classical.choose_spec (c.covers i hi)

/-- Restore precisely zero outside the retained core. -/
def extend {n r : ℕ} {X : Fin n → M2} (c : Selection n r X) (Y : Fin r → M2) : Fin n → M2 :=
  fun i => if hi : X i=0 then 0 else Y (lookup c i hi)

@[simp] theorem extend_of_zero {n r : ℕ} {X : Fin n → M2}
    (c : Selection n r X) (Y : Fin r → M2) (i : Fin n) (hi : X i=0) : extend c Y i=0 := by
  simp [extend,hi]

@[simp] theorem extend_of_ne_zero {n r : ℕ} {X : Fin n → M2}
    (c : Selection n r X) (Y : Fin r → M2) (i : Fin n) (hi : X i≠0) :
    extend c Y i=Y (lookup c i hi) := by simp [extend,hi]

@[simp] theorem extend_pick {n r : ℕ} {X : Fin n → M2}
    (c : Selection n r X) (Y : Fin r → M2) (a : Fin r) : extend c Y (c.pick a)=Y a := by
  rw [extend_of_ne_zero c Y _ (c.nonzero a)]
  have he : lookup c (c.pick a) (c.nonzero a)=a := c.injective (pick_lookup c _ _)
  rw [he]

@[simp] theorem extend_reduced {n r : ℕ} {X : Fin n → M2}
    (c : Selection n r X) : extend c (reduced c)=X := by
  funext i
  by_cases hi : X i=0
  · rw [extend_of_zero c _ i hi,hi]
  · rw [extend_of_ne_zero c _ i hi]
    exact congrArg X (pick_lookup c i hi)

/-- A selection exists for every finite family; its size is the actual number
of nonzero factors. No default core index is needed. -/
theorem exists_selection {n : ℕ} (X : Fin n → M2) : ∃ r, Nonempty (Selection n r X) := by
  classical
  let I := {i : Fin n // X i≠0}
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I,⟨{
    pick := fun a => (e.symm a).val
    injective := ?_
    nonzero := fun a => (e.symm a).property
    covers := ?_ }⟩⟩
  · intro a b h
    exact e.symm.injective (Subtype.ext h)
  · intro i hi
    exact ⟨e ⟨i,hi⟩,by simp⟩

def reducedMatrix {p q r s : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    {A : Fin p → M2} {B : Fin q → M2}
    (cA : Selection p r A) (cB : Selection q s B) : Matrix (Fin r) (Fin s) ℝ :=
  M.submatrix cA.pick cB.pick

theorem factorization_restrict {p q r s : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (cA : Selection p r A) (cB : Selection q s B) (hfact : Factorization M A B) :
    Factorization (reducedMatrix M cA cB) (reduced cA) (reduced cB) := by
  exact ⟨fun a => hfact.1 (cA.pick a),fun b => hfact.2.1 (cB.pick b),
    fun a b => hfact.2.2 (cA.pick a) (cB.pick b)⟩

theorem row_coordinate_span {p r : ℕ} {A : Fin p → M2} (c : Selection p r A) :
    Submodule.span ℝ (Set.range (leftCoordinates A).row) ≤
      Submodule.span ℝ (Set.range (leftCoordinates (reduced c)).row) := by
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  by_cases hi : A i=0
  · have hz : (leftCoordinates A).row i=0 := by
      ext a; fin_cases a <;> simp [Matrix.row,leftCoordinates,hi]
    rw [hz]
    exact Submodule.zero_mem _
  · obtain ⟨a,ha⟩ := c.covers i hi
    have hm := Submodule.subset_span (R := ℝ)
      (Set.mem_range_self (f := (leftCoordinates (reduced c)).row) a)
    have heq : (leftCoordinates (reduced c)).row a=(leftCoordinates A).row i := by
      ext k
      simp [Matrix.row,leftCoordinates,reduced,ha]
    rwa [heq] at hm

theorem column_coordinate_span {q s : ℕ} {B : Fin q → M2} (c : Selection q s B) :
    Submodule.span ℝ (Set.range (rightCoordinates B).col) ≤
      Submodule.span ℝ (Set.range (rightCoordinates (reduced c)).col) := by
  apply Submodule.span_le.mpr
  rintro x ⟨j,rfl⟩
  by_cases hj : B j=0
  · have hz : (rightCoordinates B).col j=0 := by
      ext a; fin_cases a <;> simp [Matrix.col,rightCoordinates,hj]
    rw [hz]
    exact Submodule.zero_mem _
  · obtain ⟨b,hb⟩ := c.covers j hj
    have hm := Submodule.subset_span (R := ℝ)
      (Set.mem_range_self (f := (rightCoordinates (reduced c)).col) b)
    have heq : (rightCoordinates (reduced c)).col b=(rightCoordinates B).col j := by
      ext k
      simp [Matrix.col,rightCoordinates,reduced,Function.comp_def,hb]
    rwa [heq] at hm

/-- Removing actual zero factors preserves rank exactly three. The proof
retains the actual spanning coordinate families and constructs both inverses. -/
theorem reduced_rank_three {p q r s : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → M2) (B : Fin q → M2)
    (cA : Selection p r A) (cB : Selection q s B)
    (hfact : Factorization M A B) (hrank : M.rank=3) :
    (reducedMatrix M cA cB).rank=3 := by
  have hx : Submodule.span ℝ (Set.range (leftCoordinates (reduced cA)).row)=⊤ := by
    apply top_unique
    rw [← (factorization_coordinate_spans M A B hfact hrank).1]
    exact row_coordinate_span cA
  have hy : Submodule.span ℝ (Set.range (rightCoordinates (reduced cB)).col)=⊤ := by
    apply top_unique
    rw [← (factorization_coordinate_spans M A B hfact hrank).2]
    exact column_coordinate_span cB
  obtain ⟨U,hU⟩ := left_inverse_of_row_span _ hx
  obtain ⟨V,hV⟩ := right_inverse_of_column_span _ hy
  have hred := factorization_restrict M A B cA cB hfact
  have heq : U * reducedMatrix M cA cB * V=(1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [factorization_coordinates _ _ _ hred]
    simp [← Matrix.mul_assoc,hU,hV]
  have hlo : 3≤(reducedMatrix M cA cB).rank := by
    calc
      3 = (1 : Matrix (Fin 3) (Fin 3) ℝ).rank := by simp
      _ = (U * reducedMatrix M cA cB * V).rank := by rw [heq]
      _ ≤ (U * reducedMatrix M cA cB).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (reducedMatrix M cA cB).rank := Matrix.rank_mul_le_right _ _
  have hhi : (reducedMatrix M cA cB).rank≤3 := by
    rw [factorization_coordinates _ _ _ hred]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  exact Nat.le_antisymm hhi hlo

#assert_trust kernel exists_selection
#assert_trust kernel reduced_rank_three
#print axioms reduced_rank_three
end
end ZeroRestriction
end NLA.Proofs.PF05
