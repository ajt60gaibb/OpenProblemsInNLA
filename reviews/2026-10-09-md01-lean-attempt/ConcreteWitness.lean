import GraphShapeMoment

/-!
The four concrete shapes in the counterexample pattern. The first two
are single edges; the third is a chorded four-cycle; the fourth is a
triangle. A four-vertex labeling makes every edge occur exactly twice.
-/

namespace MD01ConcreteWitness

open MD01GraphShapeMoment MD01GraphMatrix MD01GraphBits MD01UniformSigns

def edgeShape : Shape where
  k := 2
  u := 0
  v := 1
  edges := {(0, 1)}

def chordShape : Shape where
  k := 4
  u := 0
  v := 1
  edges := {(0, 2), (2, 3), (3, 1), (0, 1), (0, 3)}

def triangleShape : Shape where
  k := 3
  u := 0
  v := 1
  edges := {(0, 2), (2, 1), (0, 1)}

theorem edge_loopless : Loopless edgeShape := by
  intro e he h
  rcases e with ⟨a, b⟩
  change a = b at h
  subst b
  change (a, a) ∈ ({(0, 1)} : Finset (Fin 2 × Fin 2)) at he
  have hdiag : ∀ x : Fin 2,
      (x, x) ∉ ({(0, 1)} : Finset (Fin 2 × Fin 2)) := by decide
  exact hdiag a he
theorem chord_loopless : Loopless chordShape := by
  intro e he h
  rcases e with ⟨a, b⟩
  change a = b at h
  subst b
  change (a, a) ∈
    ({(0, 2), (2, 3), (3, 1), (0, 1), (0, 3)} : Finset (Fin 4 × Fin 4)) at he
  have hdiag : ∀ x : Fin 4,
      (x, x) ∉
        ({(0, 2), (2, 3), (3, 1), (0, 1), (0, 3)} : Finset (Fin 4 × Fin 4)) := by
    decide
  exact hdiag a he
theorem triangle_loopless : Loopless triangleShape := by
  intro e he h
  rcases e with ⟨a, b⟩
  change a = b at h
  subst b
  change (a, a) ∈ ({(0, 2), (2, 1), (0, 1)} : Finset (Fin 3 × Fin 3)) at he
  have hdiag : ∀ x : Fin 3,
      (x, x) ∉ ({(0, 2), (2, 1), (0, 1)} : Finset (Fin 3 × Fin 3)) := by decide
  exact hdiag a he

def edgeEmbedding₁ : Fin 2 ↪ Fin 4 where
  toFun := ![(0 : Fin 4), 1]
  inj' := by decide

def edgeEmbedding₂ : Fin 2 ↪ Fin 4 where
  toFun := ![(1 : Fin 4), 2]
  inj' := by decide

def chordEmbedding : Fin 4 ↪ Fin 4 where
  toFun := ![(2 : Fin 4), 3, 1, 0]
  inj' := by decide

def triangleEmbedding : Fin 3 ↪ Fin 4 where
  toFun := ![(3 : Fin 4), 0, 2]
  inj' := by decide

variable {n : ℕ}

def composedEmbedding {k : ℕ} (q : Fin 4 ↪ Fin n)
    (e : Fin k ↪ Fin 4) : Fin k ↪ Fin n where
  toFun i := q (e i)
  inj' := fun _ _ h => e.injective (q.injective h)

def witness₁ (q : Fin 4 ↪ Fin n) : Fin 2 ↪ Fin n :=
  composedEmbedding q edgeEmbedding₁
def witness₂ (q : Fin 4 ↪ Fin n) : Fin 2 ↪ Fin n :=
  composedEmbedding q edgeEmbedding₂
def witness₃ (q : Fin 4 ↪ Fin n) : Fin 4 ↪ Fin n :=
  composedEmbedding q chordEmbedding
def witness₄ (q : Fin 4 ↪ Fin n) : Fin 3 ↪ Fin n :=
  composedEmbedding q triangleEmbedding

example (q : Fin 4 ↪ Fin n) : witness₁ q 0 = q 0 := by rfl
example (q : Fin 4 ↪ Fin n) : witness₃ q 2 = q 1 := by rfl

theorem graphSign_comm (G : SimpleGraph (Fin n)) (a b : Fin n) :
    graphSign G a b = graphSign G b a := by
  by_cases h : a = b
  · subst b; rfl
  · have h' : b ≠ a := Ne.symm h
    simp only [graphSign, dif_neg h, dif_neg h']
    congr 1
    apply congrArg
    exact Subtype.ext (Sym2.eq_swap)

theorem graphSign_sq (G : SimpleGraph (Fin n)) (a b : Fin n) :
    graphSign G a b * graphSign G a b = 1 := by
  by_cases h : a = b
  · simp [graphSign, h]
  · simp only [graphSign, dif_neg h]
    cases bitsOfGraph G ⟨s(a,b), Sym2.mk_isDiag_iff.not.mpr h⟩ <;>
      norm_num [sign]

theorem concrete_four_weights_one (q : Fin 4 ↪ Fin n)
    (G : SimpleGraph (Fin n)) :
    (((weight edgeShape (graphSign G) (witness₁ q) *
        weight edgeShape (graphSign G) (witness₂ q)) *
        weight chordShape (graphSign G) (witness₃ q)) *
        weight triangleShape (graphSign G) (witness₄ q)) = 1 := by
  classical
  simp [weight, edgeShape, chordShape, triangleShape, composedEmbedding,
    witness₁, witness₂, witness₃, witness₄,
    edgeEmbedding₁, edgeEmbedding₂, chordEmbedding,
    triangleEmbedding, Function.Embedding.coeFn_mk]
  change
    (graphSign G (q 0) (q 1) * graphSign G (q 1) (q 2)) *
      (graphSign G (q 2) (q 1) *
        (graphSign G (q 1) (q 0) *
          (graphSign G (q 0) (q 3) *
            (graphSign G (q 2) (q 3) * graphSign G (q 2) (q 0))))) *
      (graphSign G (q 3) (q 2) *
        (graphSign G (q 2) (q 0) * graphSign G (q 3) (q 0))) = 1
  rw [graphSign_comm G (q 2) (q 1),
      graphSign_comm G (q 1) (q 0),
      graphSign_comm G (q 3) (q 2),
      graphSign_comm G (q 3) (q 0)]
  have hab := graphSign_sq G (q 0) (q 1)
  have hbc := graphSign_sq G (q 1) (q 2)
  have had := graphSign_sq G (q 0) (q 3)
  have hcd := graphSign_sq G (q 2) (q 3)
  have hac := graphSign_sq G (q 2) (q 0)
  calc
    _ = (graphSign G (q 0) (q 1) * graphSign G (q 0) (q 1)) *
        (graphSign G (q 1) (q 2) * graphSign G (q 1) (q 2)) *
        (graphSign G (q 0) (q 3) * graphSign G (q 0) (q 3)) *
        (graphSign G (q 2) (q 3) * graphSign G (q 2) (q 3)) *
        (graphSign G (q 2) (q 0) * graphSign G (q 2) (q 0)) := by ring
    _ = 1 := by rw [hab, hbc, had, hcd, hac]; norm_num

#print axioms edge_loopless
#print axioms chord_loopless
#print axioms triangle_loopless
#print axioms graphSign_comm
#print axioms graphSign_sq
#print axioms concrete_four_weights_one

end MD01ConcreteWitness
