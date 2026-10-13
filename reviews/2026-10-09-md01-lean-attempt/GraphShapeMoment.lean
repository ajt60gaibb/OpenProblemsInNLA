import GraphMeasureParity
import GraphMatrix

/-!
Transfer an individual loopless graph-matrix block to the actual
G(n,1/2) edge-bit measure. This isolates the edge-parity content of a
four-block mixed moment, without counting possible intersections.
-/

open MeasureTheory

namespace MD01GraphShapeMoment

open MD01UniformSigns MD01GraphBits MD01GraphMeasureParity MD01GraphMatrix MD01FullBridge

variable {n : ℕ}

def Loopless (τ : Shape) : Prop :=
  ∀ e ∈ τ.edges, e.1 ≠ e.2

def graphEdge (τ : Shape) (hτ : Loopless τ)
    (f : Fin τ.k ↪ Fin n) (e : {e // e ∈ τ.edges}) : Edge n :=
  ⟨s(f e.val.1, f e.val.2), by
    apply Sym2.mk_isDiag_iff.not.mpr
    intro h
    exact hτ e.val e.property (f.injective h)⟩

noncomputable def mappedGraphEdges (τ : Shape) (hτ : Loopless τ)
    (f : Fin τ.k ↪ Fin n) : List (Edge n) :=
  τ.edges.attach.toList.map (graphEdge τ hτ f)

noncomputable def graphSign (G : SimpleGraph (Fin n)) (a b : Fin n) : ℤ :=
  if h : a = b then 1 else
    sign (bitsOfGraph G ⟨s(a, b), Sym2.mk_isDiag_iff.not.mpr h⟩)

theorem weight_eq_graphMonomial (τ : Shape) (hτ : Loopless τ)
    (f : Fin τ.k ↪ Fin n) (G : SimpleGraph (Fin n)) :
    weight τ (graphSign G) f =
      listMonomial (mappedGraphEdges τ hτ f) (bitsOfGraph G) := by
  classical
  unfold weight mappedGraphEdges listMonomial
  rw [List.map_map]
  rw [Finset.prod_map_toList]
  rw [← Finset.prod_attach τ.edges
    (fun e => graphSign G (f e.1) (f e.2))]
  apply Finset.prod_congr rfl
  intro e he
  have hne : f e.val.1 ≠ f e.val.2 :=
    fun h => hτ e.val e.property (f.injective h)
  simp [graphSign, hne, graphEdge]

theorem four_weights_eq_graphMonomial
    (τ₁ τ₂ τ₃ τ₄ : Shape)
    (h₁ : Loopless τ₁) (h₂ : Loopless τ₂)
    (h₃ : Loopless τ₃) (h₄ : Loopless τ₄)
    (f₁ : Fin τ₁.k ↪ Fin n) (f₂ : Fin τ₂.k ↪ Fin n)
    (f₃ : Fin τ₃.k ↪ Fin n) (f₄ : Fin τ₄.k ↪ Fin n)
    (G : SimpleGraph (Fin n)) :
    (((weight τ₁ (graphSign G) f₁ * weight τ₂ (graphSign G) f₂) *
        weight τ₃ (graphSign G) f₃) * weight τ₄ (graphSign G) f₄) =
      listMonomial
        (mappedGraphEdges τ₁ h₁ f₁ ++ mappedGraphEdges τ₂ h₂ f₂ ++
         mappedGraphEdges τ₃ h₃ f₃ ++ mappedGraphEdges τ₄ h₄ f₄)
        (bitsOfGraph G) := by
  rw [weight_eq_graphMonomial τ₁ h₁,
      weight_eq_graphMonomial τ₂ h₂,
      weight_eq_graphMonomial τ₃ h₃,
      weight_eq_graphMonomial τ₄ h₄]
  simp [listMonomial, List.map_append, List.prod_append, mul_assoc]

theorem graph_four_weight_parity
    (τ₁ τ₂ τ₃ τ₄ : Shape)
    (h₁ : Loopless τ₁) (h₂ : Loopless τ₂)
    (h₃ : Loopless τ₃) (h₄ : Loopless τ₄)
    (f₁ : Fin τ₁.k ↪ Fin n) (f₂ : Fin τ₂.k ↪ Fin n)
    (f₃ : Fin τ₃.k ↪ Fin n) (f₄ : Fin τ₄.k ↪ Fin n) :
    (∫ G : SimpleGraph (Fin n),
      (((weight τ₁ (graphSign G) f₁ * weight τ₂ (graphSign G) f₂) *
        weight τ₃ (graphSign G) f₃) * weight τ₄ (graphSign G) f₄ : ℝ)
        ∂graphMeasure n) =
      if (∀ e : Edge n,
        Even (edgeCount
          (mappedGraphEdges τ₁ h₁ f₁ ++ mappedGraphEdges τ₂ h₂ f₂ ++
           mappedGraphEdges τ₃ h₃ f₃ ++ mappedGraphEdges τ₄ h₄ f₄) e))
      then 1 else 0 := by
  have hfun :
      (fun G : SimpleGraph (Fin n) =>
        (((weight τ₁ (graphSign G) f₁ * weight τ₂ (graphSign G) f₂) *
          weight τ₃ (graphSign G) f₃) * weight τ₄ (graphSign G) f₄ : ℝ)) =
      (fun G : SimpleGraph (Fin n) =>
        (listMonomial
          (mappedGraphEdges τ₁ h₁ f₁ ++ mappedGraphEdges τ₂ h₂ f₂ ++
           mappedGraphEdges τ₃ h₃ f₃ ++ mappedGraphEdges τ₄ h₄ f₄)
          (bitsOfGraph G) : ℝ)) := by
    funext G
    exact_mod_cast four_weights_eq_graphMonomial τ₁ τ₂ τ₃ τ₄ h₁ h₂ h₃ h₄ f₁ f₂ f₃ f₄ G
  rw [hfun]
  exact graph_monomial_parity _

#print axioms weight_eq_graphMonomial
#print axioms graph_four_weight_parity

end MD01GraphShapeMoment
