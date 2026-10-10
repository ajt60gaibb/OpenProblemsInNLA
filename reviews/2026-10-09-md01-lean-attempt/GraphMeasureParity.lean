import UniformSigns
import GraphBits
import GraphLower

/-!
The exact parity moment rule under mathlib's actual G(n,1/2) measure.
The underlying sign monomial is indexed by off-diagonal unordered edges;
this theorem is independent of the paper's shape-intersection enumeration.
-/

open MeasureTheory

namespace MD01GraphMeasureParity

open MD01UniformSigns MD01GraphBits MD01FullBridge

variable {n : ℕ}

theorem card_edges (n : ℕ) :
    Fintype.card (Edge n) = n.choose 2 := by
  classical
  have hp : (fun e : Sym2 (Fin n) => ¬ e.IsDiag) =
      (fun e => e ∈ (Sym2.diagSetᶜ : Set (Sym2 (Fin n)))) := by
    funext e
    apply propext
    simp [Sym2.mem_diagSet]
  calc
    Fintype.card (Edge n) =
        Fintype.card {e : Sym2 (Fin n) // e ∈ Sym2.diagSetᶜ} :=
          Fintype.card_congr (Equiv.subtypeEquivProp hp)
    _ = n.choose 2 := by
      simpa only [Fintype.card_fin] using (Sym2.card_diagSet_compl (α := Fin n))

private theorem graph_integrable (n : ℕ)
    (F : SimpleGraph (Fin n) → ℝ) : Integrable F (graphMeasure n) := by
  have hf : (Set.univ : Set (SimpleGraph (Fin n))).Finite := Set.toFinite _
  simpa only [integrableOn_univ] using
    (IntegrableOn.of_finite (μ := graphMeasure n) hf (f := F))

theorem graph_integral_uniform_sum (n : ℕ)
    (F : SimpleGraph (Fin n) → ℝ) :
    (∫ G, F G ∂graphMeasure n) =
      (∑ G : SimpleGraph (Fin n), F G) / (2 : ℝ) ^ Fintype.card (Edge n) := by
  classical
  rw [integral_fintype (graph_integrable n F)]
  simp_rw [Measure.real, graph_mass_half]
  rw [card_edges]
  simp [ENNReal.toReal_pow, div_eq_mul_inv, inv_pow, mul_comm]
  rw [Finset.sum_mul]

theorem graph_monomial_parity (L : List (Edge n)) :
    (∫ G : SimpleGraph (Fin n),
      (listMonomial L (bitsOfGraph G) : ℝ) ∂graphMeasure n) =
        if (∀ e : Edge n, Even (edgeCount L e)) then 1 else 0 := by
  classical
  rw [graph_integral_uniform_sum]
  have hsum : (∑ G : SimpleGraph (Fin n),
      (listMonomial L (bitsOfGraph G) : ℝ)) =
      (rawListMoment L : ℝ) := by
    rw [← (graphBitsEquiv n).sum_comp
      (fun G : SimpleGraph (Fin n) => (listMonomial L (bitsOfGraph G) : ℝ))]
    change (∑ ξ : Edge n → Bool,
      (listMonomial L (bitsOfGraph (graphOfBits ξ)) : ℝ)) = _
    simp_rw [bitsOfGraph_graphOfBits]
    exact (Int.cast_sum _ _).symm
  rw [hsum]
  let P : Prop := ∀ e : Edge n, Even (edgeCount L e)
  have hraw : rawListMoment L =
      if P then (2 : ℤ) ^ Fintype.card (Edge n) else 0 :=
    by simpa only [P] using (rawListMoment_eq_if_even L)
  change ((rawListMoment L : ℝ) / (2 : ℝ) ^ Fintype.card (Edge n)) =
    if P then 1 else 0
  calc
    (rawListMoment L : ℝ) / (2 : ℝ) ^ Fintype.card (Edge n) =
        ((if P then (2 : ℤ) ^ Fintype.card (Edge n) else 0 : ℤ) : ℝ) /
          (2 : ℝ) ^ Fintype.card (Edge n) :=
            congrArg (fun z : ℤ => (z : ℝ) / (2 : ℝ) ^ Fintype.card (Edge n)) hraw
    _ = if P then 1 else 0 := by
      by_cases h : P <;> simp [h]

#print axioms card_edges
#print axioms graph_integral_uniform_sum
#print axioms graph_monomial_parity

end MD01GraphMeasureParity
