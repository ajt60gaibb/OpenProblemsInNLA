import Mathlib
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Filter unitInterval Matrix

namespace MD01Scratch

/-- A faithful SDP encoding of the Lovász theta number in the problem statement. -/
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

namespace MD01Scratch

private theorem neg_two_mul_entry_le_diag {n : ℕ}
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef) (i j : Fin n) :
    -(2 * X i j) ≤ X i i + X j j := by
  classical
  let e : Fin 2 → Fin n := fun k => if k = 0 then i else j
  have hq := (hX.submatrix e).dotProduct_mulVec_nonneg ![(1:ℝ), 1]
  have hsym : X j i = X i j := by
    have hh := hX.isHermitian
    exact congrFun (congrFun hh i) j
  simp [e] at hq
  linarith

#print axioms MD01Scratch.neg_two_mul_entry_le_diag

end MD01Scratch

namespace MD01Scratch

private theorem diag_le_one {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (htr : X.trace = 1) (i : Fin n) : X i i ≤ 1 := by
  have hsum : X i i ≤ ∑ k, X k k :=
    Finset.single_le_sum (s := Finset.univ) (f := fun k : Fin n => X k k)
      (fun k _ => hX.diag_nonneg) (Finset.mem_univ i)
  simpa only [Matrix.trace] using hsum.trans_eq htr

#print axioms MD01Scratch.diag_le_one

end MD01Scratch

namespace MD01Scratch

private theorem entry_mem_Icc {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (htr : X.trace = 1) (i j : Fin n) :
    X i j ∈ Set.Icc (-1 : ℝ) 1 := by
  have hu := two_mul_entry_le_diag hX i j
  have hl := neg_two_mul_entry_le_diag hX i j
  have hii := diag_le_one hX htr i
  have hjj := diag_le_one hX htr j
  constructor <;> linarith

#print axioms MD01Scratch.entry_mem_Icc

end MD01Scratch

namespace MD01Scratch

private theorem isClosed_posSemidef (n : ℕ) :
    IsClosed {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef} := by
  have hherm : IsClosed {X : Matrix (Fin n) (Fin n) ℝ | X.IsHermitian} := by
    exact isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id
  have hquad (x : Fin n → ℝ) :
      IsClosed {X : Matrix (Fin n) (Fin n) ℝ | 0 ≤ star x ⬝ᵥ (X *ᵥ x)} := by
    exact isClosed_le continuous_const (by fun_prop)
  have hall : IsClosed {X : Matrix (Fin n) (Fin n) ℝ |
      ∀ x : Fin n → ℝ, 0 ≤ star x ⬝ᵥ (X *ᵥ x)} := by
    simpa only [Set.ofPred_forall] using isClosed_iInter hquad
  convert hherm.inter hall using 1
  ext X
  simp [Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian]

#print axioms MD01Scratch.isClosed_posSemidef

end MD01Scratch

namespace MD01Scratch

private def feasible {n : ℕ} (G : SimpleGraph (Fin n)) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | X.PosSemidef ∧ X.trace = 1 ∧ ∀ i j, G.Adj i j → X i j = 0}

private theorem isClosed_feasible {n : ℕ} (G : SimpleGraph (Fin n)) :
    IsClosed (feasible G) := by
  have hpsd := isClosed_posSemidef n
  have htr : IsClosed {X : Matrix (Fin n) (Fin n) ℝ | X.trace = 1} := by
    exact isClosed_eq (by unfold Matrix.trace; fun_prop) continuous_const
  have hedge (i j : Fin n) :
      IsClosed {X : Matrix (Fin n) (Fin n) ℝ | G.Adj i j → X i j = 0} := by
    by_cases hij : G.Adj i j
    · simpa [hij] using
        (isClosed_eq (continuous_id.matrix_elem i j) continuous_const)
    · simp [hij]
  have hedges : IsClosed {X : Matrix (Fin n) (Fin n) ℝ |
      ∀ i j, G.Adj i j → X i j = 0} := by
    simpa only [Set.ofPred_forall] using
      isClosed_iInter (fun i => isClosed_iInter (hedge i))
  convert hpsd.inter (htr.inter hedges) using 1
  ext X
  simp [feasible]

#print axioms MD01Scratch.isClosed_feasible

end MD01Scratch

namespace MD01Scratch

private theorem isCompact_feasible {n : ℕ} (G : SimpleGraph (Fin n)) :
    IsCompact (feasible G) := by
  have hbox : IsCompact ((Set.Icc (-1 : ℝ) 1).matrix :
      Set (Matrix (Fin n) (Fin n) ℝ)) := isCompact_Icc.matrix
  apply hbox.of_isClosed_subset (isClosed_feasible G)
  intro X hX
  exact fun i j => entry_mem_Icc hX.1 hX.2.1 i j

#print axioms MD01Scratch.isCompact_feasible

end MD01Scratch

namespace MD01Scratch

private theorem isClosed_theta_values {n : ℕ} (G : SimpleGraph (Fin n)) :
    IsClosed {v : ℝ | ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X.PosSemidef ∧ X.trace = 1 ∧
      (∀ i j, G.Adj i j → X i j = 0) ∧
      v = ∑ i, ∑ j, X i j} := by
  have hcont : Continuous (fun X : Matrix (Fin n) (Fin n) ℝ =>
      ∑ i, ∑ j, X i j) := by fun_prop
  have himage := ((isCompact_feasible G).image hcont).isClosed
  convert himage using 1
  ext v
  constructor
  · rintro ⟨X, hpsd, htr, hedge, hv⟩
    exact ⟨X, ⟨hpsd, htr, hedge⟩, hv.symm⟩
  · rintro ⟨X, ⟨hpsd, htr, hedge⟩, hv⟩
    exact ⟨X, hpsd, htr, hedge, hv.symm⟩

#print axioms MD01Scratch.isClosed_theta_values

end MD01Scratch

namespace MD01Scratch

/-- For every graph of positive order, the canonical theta SDP has a maximizer. -/
theorem theta_max_attained {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X.PosSemidef ∧ X.trace = 1 ∧
      (∀ i j, G.Adj i j → X i j = 0) ∧
      theta G = ∑ i, ∑ j, X i j := by
  exact (isClosed_theta_values G).csSup_mem
    (theta_domain_nonempty n hn G) (theta_domain_bddAbove n G)

#print axioms MD01Scratch.theta_max_attained

end MD01Scratch

namespace MD01Scratch

/-- The attained value is the maximum of the original trace-normalized SDP. -/
theorem theta_eq_canonical_max {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X.PosSemidef ∧ X.trace = 1 ∧
      (∀ i j, G.Adj i j → X i j = 0) ∧
      (∀ Y : Matrix (Fin n) (Fin n) ℝ,
        Y.PosSemidef → Y.trace = 1 →
        (∀ i j, G.Adj i j → Y i j = 0) →
        (∑ i, ∑ j, Y i j) ≤ ∑ i, ∑ j, X i j) ∧
      theta G = ∑ i, ∑ j, X i j := by
  obtain ⟨X, hpsd, htr, hedge, htheta⟩ := theta_max_attained hn G
  refine ⟨X, hpsd, htr, hedge, ?_, htheta⟩
  intro Y hY hYtr hYedge
  rw [← htheta]
  exact le_csSup (theta_domain_bddAbove n G) ⟨Y, hY, hYtr, hYedge, rfl⟩

#print axioms MD01Scratch.theta_eq_canonical_max

end MD01Scratch
