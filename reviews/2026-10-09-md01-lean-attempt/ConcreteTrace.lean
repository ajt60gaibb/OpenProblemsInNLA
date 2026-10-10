import ConcreteWitness

-- Probability-measure instances below are local proof values.
set_option linter.style.haveILetI false

/-!
Tie the four-shape witness to the complete cyclic graph-matrix trace.
The proof keeps every injective block labeling as a separate term.
-/

open MeasureTheory

namespace MD01ConcreteTrace

open MD01ConcreteWitness MD01GraphShapeMoment MD01GraphMatrix MD01FullBridge

variable {n : ℕ}

abbrev TraceIndex (n : ℕ) :=
  Fin n × (Fin n × (Fin n × (Fin n ×
    ((Fin 3 ↪ Fin n) × ((Fin 4 ↪ Fin n) ×
      ((Fin 2 ↪ Fin n) × (Fin 2 ↪ Fin n)))))))

noncomputable def traceTerm (G : SimpleGraph (Fin n)) : TraceIndex n → ℤ
  | ⟨a, d, c, b, f₄, f₃, f₂, f₁⟩ =>
    (((if f₁ edgeShape.u = a ∧ f₁ edgeShape.v = b
       then weight edgeShape (graphSign G) f₁ else 0) *
      (if f₂ edgeShape.u = b ∧ f₂ edgeShape.v = c
       then weight edgeShape (graphSign G) f₂ else 0)) *
      (if f₃ chordShape.u = c ∧ f₃ chordShape.v = d
       then weight chordShape (graphSign G) f₃ else 0)) *
      (if f₄ triangleShape.u = d ∧ f₄ triangleShape.v = a
       then weight triangleShape (graphSign G) f₄ else 0)

theorem trace_eq_sum_terms (G : SimpleGraph (Fin n)) :
    Matrix.trace (((graphMatrix edgeShape (graphSign G) *
        graphMatrix edgeShape (graphSign G)) *
        graphMatrix chordShape (graphSign G)) *
        graphMatrix triangleShape (graphSign G)) =
      ∑ i : TraceIndex n, traceTerm G i := by
  classical
  rw [trace_four_graph_expand]
  simp only [Fintype.sum_prod_type, traceTerm]
  rfl

def witnessIndex (q : Fin 4 ↪ Fin n) : TraceIndex n :=
  ⟨q 0, q 3, q 2, q 1,
    witness₄ q, witness₃ q, witness₂ q, witness₁ q⟩

theorem witnessIndex_injective : Function.Injective (witnessIndex (n := n)) := by
  intro q r h
  have h0 : q 0 = r 0 := congrArg (fun i : TraceIndex n => i.1) h
  have h3 : q 3 = r 3 := congrArg (fun i : TraceIndex n => i.2.1) h
  have h2 : q 2 = r 2 := congrArg (fun i : TraceIndex n => i.2.2.1) h
  have h1 : q 1 = r 1 := congrArg (fun i : TraceIndex n => i.2.2.2.1) h
  apply Function.Embedding.ext
  intro x
  fin_cases x
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · simpa using h3

theorem traceTerm_witness (q : Fin 4 ↪ Fin n)
    (G : SimpleGraph (Fin n)) : traceTerm G (witnessIndex q) = 1 := by
  have h₁ : witness₁ q edgeShape.u = q 0 ∧ witness₁ q edgeShape.v = q 1 :=
    ⟨rfl, rfl⟩
  have h₂ : witness₂ q edgeShape.u = q 1 ∧ witness₂ q edgeShape.v = q 2 :=
    ⟨rfl, rfl⟩
  have h₃ : witness₃ q chordShape.u = q 2 ∧ witness₃ q chordShape.v = q 3 :=
    ⟨rfl, rfl⟩
  have h₄ : witness₄ q triangleShape.u = q 3 ∧ witness₄ q triangleShape.v = q 0 :=
    ⟨rfl, rfl⟩
  simp only [traceTerm, witnessIndex, h₁, h₂, h₃, h₄]
  exact concrete_four_weights_one q G

noncomputable def termMoment (i : TraceIndex n) : ℝ :=
  ∫ G : SimpleGraph (Fin n), (traceTerm G i : ℝ) ∂graphMeasure n

theorem termMoment_nonneg (i : TraceIndex n) : 0 ≤ termMoment i := by
  rcases i with ⟨a, d, c, b, f₄, f₃, f₂, f₁⟩
  by_cases h₁ : f₁ edgeShape.u = a ∧ f₁ edgeShape.v = b <;>
    by_cases h₂ : f₂ edgeShape.u = b ∧ f₂ edgeShape.v = c <;>
    by_cases h₃ : f₃ chordShape.u = c ∧ f₃ chordShape.v = d <;>
    by_cases h₄ : f₄ triangleShape.u = d ∧ f₄ triangleShape.v = a
  all_goals
    simp only [termMoment, traceTerm, h₁, h₂, h₃, h₄,
      and_true, ite_true, ite_false, zero_mul, mul_zero,
      Int.cast_zero, integral_zero, le_refl]
  simp only [Int.cast_mul]
  rw [graph_four_weight_parity edgeShape edgeShape chordShape triangleShape
    edge_loopless edge_loopless chord_loopless triangle_loopless
    f₁ f₂ f₃ f₄]
  split_ifs <;> norm_num

theorem termMoment_witness (q : Fin 4 ↪ Fin n) :
    termMoment (witnessIndex q) = 1 := by
  haveI : IsProbabilityMeasure (graphMeasure n) := by
    unfold graphMeasure
    infer_instance
  unfold termMoment
  simp_rw [traceTerm_witness q]
  simp

noncomputable def traceInt (G : SimpleGraph (Fin n)) : ℤ :=
  Matrix.trace (((graphMatrix edgeShape (graphSign G) *
    graphMatrix edgeShape (graphSign G)) *
    graphMatrix chordShape (graphSign G)) *
    graphMatrix triangleShape (graphSign G))

noncomputable def traceMoment (n : ℕ) : ℝ :=
  ∫ G : SimpleGraph (Fin n), (traceInt G : ℝ) ∂graphMeasure n

theorem traceMoment_eq_sum (n : ℕ) :
    traceMoment n = ∑ i : TraceIndex n, termMoment i := by
  classical
  unfold traceMoment termMoment traceInt
  simp_rw [trace_eq_sum_terms]
  simp_rw [Int.cast_sum]
  rw [integral_finsetSum]
  intro i hi
  have hf : (Set.univ : Set (SimpleGraph (Fin n))).Finite := Set.toFinite _
  simpa only [integrableOn_univ] using
    (IntegrableOn.of_finite (μ := graphMeasure n) hf
      (f := fun G : SimpleGraph (Fin n) => (traceTerm G i : ℝ)))

/-- The expected unnormalized four-block trace includes at least one
parity-even contribution per injective four-vertex labeling. -/
theorem traceMoment_ge_embeddings (n : ℕ) :
    (Fintype.card (Fin 4 ↪ Fin n) : ℝ) ≤ traceMoment n := by
  classical
  rw [traceMoment_eq_sum]
  let w : (Fin 4 ↪ Fin n) → TraceIndex n := witnessIndex
  have hw : Function.Injective w := witnessIndex_injective
  calc
    (Fintype.card (Fin 4 ↪ Fin n) : ℝ) =
        ∑ q : Fin 4 ↪ Fin n, (1 : ℝ) := by simp
    _ = ∑ q : Fin 4 ↪ Fin n, termMoment (w q) := by
      simp [w, termMoment_witness]
    _ = ∑ i ∈ (Finset.univ.image w), termMoment i := by
      rw [Finset.sum_image (s := Finset.univ) (g := w) (f := termMoment)
        (by intro x hx y hy hxy; exact hw hxy)]
    _ ≤ ∑ i : TraceIndex n, termMoment i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i hi hnot
      exact termMoment_nonneg i

theorem traceMoment_ge_descFactorial (n : ℕ) :
    (n.descFactorial 4 : ℝ) ≤ traceMoment n := by
  simpa only [Fintype.card_embedding_eq, Fintype.card_fin] using
    (traceMoment_ge_embeddings n)

#print axioms trace_eq_sum_terms
#print axioms witnessIndex_injective
#print axioms traceTerm_witness
#print axioms termMoment_nonneg
#print axioms termMoment_witness
#print axioms traceMoment_eq_sum
#print axioms traceMoment_ge_embeddings
#print axioms traceMoment_ge_descFactorial

end MD01ConcreteTrace
