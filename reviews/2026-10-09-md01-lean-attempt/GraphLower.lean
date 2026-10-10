import Mathlib
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs

open MeasureTheory unitInterval

namespace MD01FullBridge


noncomputable def half : I := ⟨(1 / 2 : ℝ), by norm_num⟩

noncomputable def graphMeasure (n : ℕ) : Measure (SimpleGraph (Fin n)) :=
  SimpleGraph.binomialRandom (Fin n) half

private instance graphProbability (n : ℕ) : IsProbabilityMeasure (graphMeasure n) := by
  unfold graphMeasure
  infer_instance

theorem graph_mass_half (n : ℕ) (G : SimpleGraph (Fin n)) :
    graphMeasure n {G} = (1 / 2 : ENNReal) ^ (n.choose 2) := by
  classical
  rw [graphMeasure, SimpleGraph.binomialRandom_singleton]
  have hhalf1 : ((toNNReal half : NNReal) : ENNReal) = 1 / 2 := by
    have h : toNNReal half = (1 / 2 : NNReal) := by
      apply Subtype.ext
      norm_num [half, toNNReal]
    rw [h]
    norm_num
  have hhalf2 : ((toNNReal (σ half) : NNReal) : ENNReal) = 1 / 2 := by
    have h : toNNReal (σ half) = (1 / 2 : NNReal) := by
      apply Subtype.ext
      norm_num [half, toNNReal, unitInterval.symm]
    rw [h]
    norm_num
  rw [hhalf1, hhalf2]
  norm_num [Nat.card_fin]
  have hcard : G.edgeSet.ncard ≤ n.choose 2 := by
    simpa [Sym2.ncard_diagSet_compl, Nat.card_fin] using
      (Set.ncard_le_ncard G.edgeSet_subset_compl_diagSet)
  rw [← pow_add, Nat.add_sub_of_le hcard]

private def graphComplEquiv (n : ℕ) :
    SimpleGraph (Fin n) ≃ SimpleGraph (Fin n) where
  toFun G := Gᶜ
  invFun G := Gᶜ
  left_inv G := by simp
  right_inv G := by simp

private instance graphMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (SimpleGraph (Fin n)) := ⟨fun G => by
    have hs : MeasurableSet ({G.edgeSet} : Set (Set (Sym2 (Fin n)))) :=
      measurableSet_singleton _
    have hm := (SimpleGraph.measurable_edgeSet (V := Fin n)) hs
    convert hm using 1
    ext H
    simp [SimpleGraph.edgeSet_injective.eq_iff]
  ⟩

private theorem graph_integrable (n : ℕ) (f : SimpleGraph (Fin n) → ℝ) :
    Integrable f (graphMeasure n) := by
  have hf : (Set.univ : Set (SimpleGraph (Fin n))).Finite := Set.toFinite _
  simpa only [integrableOn_univ] using
    (IntegrableOn.of_finite (μ := graphMeasure n) hf (f := f))

theorem integral_graph_compl (n : ℕ) (f : SimpleGraph (Fin n) → ℝ) :
    (∫ G, f Gᶜ ∂graphMeasure n) = ∫ G, f G ∂graphMeasure n := by
  classical
  rw [integral_fintype (graph_integrable n (fun G => f Gᶜ)),
    integral_fintype (graph_integrable n f)]
  simp_rw [Measure.real, graph_mass_half]
  simpa [graphComplEquiv] using
    (graphComplEquiv n).sum_comp
      (fun G => ((1 / 2 : ENNReal) ^ (n.choose 2)).toReal • f G)

theorem graph_expectation_lower_from_product (n : ℕ)
    (f : SimpleGraph (Fin n) → ℝ)
    (hpos : ∀ G, 0 ≤ f G)
    (hprod : ∀ G, (n : ℝ) ≤ f G * f Gᶜ) :
    Real.sqrt n ≤ ∫ G, f G ∂graphMeasure n := by
  have hp (G : SimpleGraph (Fin n)) :
      2 * Real.sqrt n ≤ f G + f Gᶜ := by
    have hn' : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
    have hr : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have ha := hpos G
    have hb := hpos Gᶜ
    have hsq : (2 * Real.sqrt n) ^ 2 ≤ (f G + f Gᶜ) ^ 2 := by
      nlinarith [sq_nonneg (f G - f Gᶜ), hprod G]
    nlinarith
  have hi : (∫ _G : SimpleGraph (Fin n), (2 * Real.sqrt n : ℝ) ∂graphMeasure n)
      ≤ ∫ G, f G + f Gᶜ ∂graphMeasure n := by
    apply integral_mono (integrable_const _) (graph_integrable n _) hp
  rw [integral_const, integral_add (graph_integrable n f)
      (graph_integrable n (fun G => f Gᶜ)), integral_graph_compl] at hi
  simp at hi
  linarith

#print axioms graph_mass_half
#print axioms integral_graph_compl
#print axioms graph_expectation_lower_from_product

end MD01FullBridge
