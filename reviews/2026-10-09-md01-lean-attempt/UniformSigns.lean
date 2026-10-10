import Mathlib

/-!
Finite independent Rademacher signs.  This is a general probabilistic
ingredient of the graph-matrix trace argument: uniform averaging over all
edge-sign assignments kills a monomial precisely when some edge has odd
multiplicity.  The file does not identify a paper-specific shape product
with a monomial or count the admissible intersection patterns.
-/

namespace MD01UniformSigns

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The paper's signed adjacency convention: +1 for an edge, -1 for a nonedge. -/
def sign (b : Bool) : ℤ := if b then 1 else -1

noncomputable def rawMoment (m : E → ℕ) : ℤ :=
  ∑ σ : E → Bool, ∏ e : E, sign (σ e) ^ m e

theorem rawMoment_factor (m : E → ℕ) :
    rawMoment m = ∏ e : E, (1 + (-1 : ℤ) ^ m e) := by
  classical
  have h := Finset.sum_prod_piFinset (ι := E) (s := (Finset.univ : Finset Bool))
    (g := fun e b => sign b ^ m e)
  simp only [Fintype.piFinset_univ] at h
  rw [rawMoment, h]
  simp [sign]

theorem rawMoment_even (m : E → ℕ) (hm : ∀ e, Even (m e)) :
    rawMoment m = (2 : ℤ) ^ Fintype.card E := by
  rw [rawMoment_factor]
  have hterm (e : E) : (1 : ℤ) + (-1 : ℤ) ^ m e = 2 := by
    rw [(hm e).neg_one_pow]
    norm_num
  simp_rw [hterm]
  simp

theorem rawMoment_odd (m : E → ℕ) (e : E) (he : Odd (m e)) :
    rawMoment m = 0 := by
  rw [rawMoment_factor]
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  rw [he.neg_one_pow]
  ring

theorem rawMoment_eq_if_even (m : E → ℕ) :
    rawMoment m = if (∀ e, Even (m e)) then (2 : ℤ) ^ Fintype.card E else 0 := by
  split_ifs with h
  · exact rawMoment_even m h
  · push Not at h
    obtain ⟨e, he⟩ := h
    exact rawMoment_odd m e (Nat.not_even_iff_odd.mp he)

def listMonomial (L : List E) (σ : E → Bool) : ℤ :=
  (L.map fun e => sign (σ e)).prod

/-- Count with the `DecidableEq` instance used by the generic finite-edge
theory.  Naming this avoids a different `BEq` instance at concrete subtype
edge types. -/
def edgeCount (L : List E) (e : E) : ℕ := L.count e

theorem listMonomial_eq_count (L : List E) (σ : E → Bool) :
    listMonomial L σ = ∏ e : E, sign (σ e) ^ edgeCount L e := by
  classical
  rw [listMonomial, Finset.prod_list_map_count]
  simp only [edgeCount]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro e he hnot
  have hnot' : e ∉ L := by simpa using hnot
  simp [List.count_eq_zero_of_not_mem hnot']

noncomputable def rawListMoment (L : List E) : ℤ :=
  ∑ σ : E → Bool, listMonomial L σ

/-- Exact parity rule for an arbitrary finite sequence of edges, allowing
repeated edges and collisions between shape blocks. -/
theorem rawListMoment_eq_if_even (L : List E) :
    rawListMoment L =
      if (∀ e : E, Even (edgeCount L e)) then (2 : ℤ) ^ Fintype.card E else 0 := by
  rw [rawListMoment]
  simp_rw [listMonomial_eq_count]
  exact rawMoment_eq_if_even (edgeCount L)

noncomputable def averageListMoment (L : List E) : ℚ :=
  (rawListMoment L : ℚ) / (2 : ℚ) ^ Fintype.card E

/-- A monomial in independent uniform edge signs has expectation one if
all edge multiplicities are even, and zero otherwise. -/
theorem averageListMoment_eq_if_even (L : List E) :
    averageListMoment L = if (∀ e : E, Even (edgeCount L e)) then 1 else 0 := by
  rw [averageListMoment, rawListMoment_eq_if_even]
  split_ifs <;> simp

theorem averageListMoment_nonneg (L : List E) :
    0 ≤ averageListMoment L := by
  rw [averageListMoment_eq_if_even]
  split_ifs <;> norm_num

#print axioms rawMoment_factor
#print axioms rawMoment_even
#print axioms rawMoment_odd
#print axioms rawMoment_eq_if_even
#print axioms listMonomial_eq_count
#print axioms rawListMoment_eq_if_even
#print axioms averageListMoment_eq_if_even
#print axioms averageListMoment_nonneg

end MD01UniformSigns
