import Mathlib
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Filter unitInterval

namespace MD01Scratch

/-- SDP supremum candidate corresponding to the Lovász theta number in the problem statement. -/
noncomputable def theta {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  sSup {v : ℝ | ∃ X : Matrix (Fin n) (Fin n) ℝ,
    X.PosSemidef ∧ X.trace = 1 ∧
      (∀ i j, G.Adj i j → X i j = 0) ∧
      v = ∑ i, ∑ j, X i j}

/-- The original MD-01 expectation limit, with the graph sampled from G(n,1/2). -/
def sharpThetaExpectation : Prop :=
  Tendsto (fun n : ℕ =>
    (∫ G : SimpleGraph (Fin n), theta G ∂(SimpleGraph.binomialRandom (Fin n) (⟨(1 / 2 : ℝ), by norm_num⟩ : I))) /
      Real.sqrt n) atTop (nhds 1)

#check theta
#check sharpThetaExpectation

end MD01Scratch

#print axioms MD01Scratch.theta
#print axioms MD01Scratch.sharpThetaExpectation

namespace MD01Scratch

/-- The feasible-value set in the theta SDP is nonempty for every positive order. -/
theorem theta_domain_nonempty (n : ℕ) (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    Set.Nonempty {v : ℝ | ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X.PosSemidef ∧ X.trace = 1 ∧
      (∀ i j, G.Adj i j → X i j = 0) ∧
      v = ∑ i, ∑ j, X i j} := by
  let k : Fin n := ⟨0, hn⟩
  let X : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => if i = k then 1 else 0)
  refine ⟨∑ i, ∑ j, X i j, X, ?_, ?_, ?_, rfl⟩
  · apply Matrix.PosSemidef.diagonal
    intro i
    dsimp
    split_ifs <;> norm_num
  · simp [X, Matrix.trace_diagonal, k]
  · intro i j hij
    have hne : i ≠ j := G.ne_of_adj hij
    simp [X, hne]

#print axioms MD01Scratch.theta_domain_nonempty

end MD01Scratch

namespace MD01Scratch

private instance graphMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (SimpleGraph (Fin n)) := ⟨fun G => by
    have hs : MeasurableSet ({G.edgeSet} : Set (Set (Sym2 (Fin n)))) :=
      measurableSet_singleton _
    have hm := (SimpleGraph.measurable_edgeSet (V := Fin n)) hs
    convert hm using 1
    ext H
    simp [SimpleGraph.edgeSet_injective.eq_iff]
  ⟩

theorem theta_integrable (n : ℕ) :
    Integrable (fun G : SimpleGraph (Fin n) => theta G)
      (SimpleGraph.binomialRandom (Fin n) (⟨(1 / 2 : ℝ), by norm_num⟩ : I)) := by
  have hf : (Set.univ : Set (SimpleGraph (Fin n))).Finite := Set.toFinite _
  simpa only [integrableOn_univ] using
    (IntegrableOn.of_finite (μ := SimpleGraph.binomialRandom (Fin n)
      (⟨(1 / 2 : ℝ), by norm_num⟩ : I)) hf
      (f := fun G : SimpleGraph (Fin n) => theta G))

#print axioms MD01Scratch.theta_integrable

end MD01Scratch

namespace MD01Scratch

private theorem two_mul_entry_le_diag {n : ℕ}
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef) (i j : Fin n) :
    2 * X i j ≤ X i i + X j j := by
  classical
  let e : Fin 2 → Fin n := fun k => if k = 0 then i else j
  have hq := (hX.submatrix e).dotProduct_mulVec_nonneg ![(1:ℝ), -1]
  have hsym : X j i = X i j := by
    have hh := hX.isHermitian
    exact congrFun (congrFun hh i) j
  simp [e] at hq
  linarith

#print axioms MD01Scratch.two_mul_entry_le_diag

end MD01Scratch

namespace MD01Scratch

private theorem feasible_objective_le_card {n : ℕ}
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef) (htr : X.trace = 1) :
    (∑ i, ∑ j, X i j) ≤ n := by
  classical
  have hsum : (∑ i, ∑ j, (2:ℝ) * X i j) ≤
      ∑ i, ∑ j, (X i i + X j j) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact two_mul_entry_le_diag hX i j
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp [Matrix.trace, ← Finset.mul_sum] at hsum htr
  rw [htr] at hsum
  norm_num at hsum
  linarith

#print axioms MD01Scratch.feasible_objective_le_card

end MD01Scratch

namespace MD01Scratch

/-- Every feasible objective is at most the number of vertices. -/
theorem theta_domain_bddAbove (n : ℕ) (G : SimpleGraph (Fin n)) :
    BddAbove {v : ℝ | ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X.PosSemidef ∧ X.trace = 1 ∧
      (∀ i j, G.Adj i j → X i j = 0) ∧
      v = ∑ i, ∑ j, X i j} := by
  refine ⟨n, ?_⟩
  rintro v ⟨X, hpsd, htr, _, rfl⟩
  exact feasible_objective_le_card hpsd htr

#print axioms MD01Scratch.theta_domain_bddAbove

end MD01Scratch
