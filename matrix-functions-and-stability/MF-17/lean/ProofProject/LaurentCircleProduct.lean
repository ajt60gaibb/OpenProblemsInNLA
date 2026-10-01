import ProofProject.BasisEnergy
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Finite Laurent products on the normalized additive circle

Multiplication by a reverse-frequency vector polynomial shifts a scalar
frequency `m` to `m-j`. Its coefficient at `q` is therefore the synthesis of
the scalars `c (q+j)`. Every expansion is finite and works over any finite
superset of the possible frequencies, including the original set after a
coefficient truncation.
-/

noncomputable section

open scoped BigOperators

namespace ProofProject

/-- A finitely supported scalar Laurent polynomial on the circle of period one. -/
def laurentCirclePolynomial (c : ℤ →₀ ℂ) (z : AddCircle (1 : ℝ)) : ℂ :=
  ∑ m ∈ c.support, c m * fourier (T := (1 : ℝ)) m z

universe u

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H] {n : ℕ}

/-- Reverse frequencies make nonnegative truncation correspond to coefficient tails. -/
def reverseCirclePolynomial (v : Fin n → H) (z : AddCircle (1 : ℝ)) : H :=
  ∑ j : Fin n, fourier (T := (1 : ℝ)) (-(j.val : ℤ)) z • v j

/-- The exact vector coefficient of the Laurent product at frequency `q`. -/
def laurentProductCoefficient (c : ℤ →₀ ℂ) (v : Fin n → H) (q : ℤ) : H :=
  finiteSynthesis v (fun j => c (q + (j.val : ℤ)))

/-- Every possible difference between a scalar frequency and a vector index. -/
def laurentProductFrequencies (c : ℤ →₀ ℂ) (n : ℕ) : Finset ℤ :=
  c.support.biUnion (fun m => Finset.univ.image (fun j : Fin n => m - (j.val : ℤ)))

lemma sub_mem_laurentProductFrequencies (c : ℤ →₀ ℂ) {m : ℤ}
    (hm : m ∈ c.support) (j : Fin n) :
    m - (j.val : ℤ) ∈ laurentProductFrequencies c n := by
  exact Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩

lemma laurentProductCoefficient_eq_zero_of_not_mem (c : ℤ →₀ ℂ) (v : Fin n → H)
    {q : ℤ} (hq : q ∉ laurentProductFrequencies c n) :
    laurentProductCoefficient c v q = 0 := by
  unfold laurentProductCoefficient finiteSynthesis
  apply Finset.sum_eq_zero
  intro j _
  have hc : c (q + (j.val : ℤ)) = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hm
    have hh := sub_mem_laurentProductFrequencies c hm j
    exact hq (by simpa only [add_sub_cancel_right] using hh)
  simp only [hc, zero_smul]

lemma laurentProductFrequencies_filter_subset (c : ℤ →₀ ℂ) (n : ℕ)
    (p : ℤ → Prop) [DecidablePred p] :
    laurentProductFrequencies (c.filter p) n ⊆ laurentProductFrequencies c n := by
  intro q hq
  obtain ⟨m, hm, hmq⟩ := Finset.mem_biUnion.mp hq
  rw [Finsupp.support_filter] at hm
  exact Finset.mem_biUnion.mpr ⟨m, (Finset.mem_filter.mp hm).1, hmq⟩

private lemma laurent_shift_sum (c : ℤ →₀ ℂ) (j : ℤ) (x : H)
    (s : Finset ℤ) (hs : ∀ m ∈ c.support, m - j ∈ s) (z : AddCircle (1 : ℝ)) :
    (∑ m ∈ c.support, fourier (T := (1 : ℝ)) (m - j) z • (c m • x)) =
      ∑ q ∈ s, fourier (T := (1 : ℝ)) q z • (c (q + j) • x) := by
  classical
  have hsubset : c.support.image (fun m => m - j) ⊆ s := by
    intro q hq
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hq
    exact hs m hm
  calc
    _ = ∑ q ∈ c.support.image (fun m => m - j),
        fourier (T := (1 : ℝ)) q z • (c (q + j) • x) := by
      rw [Finset.sum_image]
      · simp only [sub_add_cancel]
      · intro m _ k _ hmk
        exact sub_left_inj.mp hmk
    _ = _ := by
      apply Finset.sum_subset hsubset
      intro q _ hq
      have hc : c (q + j) = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro hm
        apply hq
        exact Finset.mem_image.mpr ⟨q + j, hm, add_sub_cancel_right q j⟩
      simp only [hc, zero_smul, smul_zero]

/-- The exact finite product expansion, over any common frequency set. -/
theorem laurentCirclePolynomial_smul_reverse (c : ℤ →₀ ℂ) (v : Fin n → H)
    (s : Finset ℤ) (hs : laurentProductFrequencies c n ⊆ s)
    (z : AddCircle (1 : ℝ)) :
    laurentCirclePolynomial c z • reverseCirclePolynomial v z =
      ∑ q ∈ s, fourier (T := (1 : ℝ)) q z • laurentProductCoefficient c v q := by
  classical
  unfold laurentCirclePolynomial reverseCirclePolynomial laurentProductCoefficient finiteSynthesis
  rw [Finset.sum_smul]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ∑ m ∈ c.support,
        fourier (T := (1 : ℝ)) (m - (j.val : ℤ)) z • (c m • v j) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [sub_eq_add_neg, fourier_add]
      simp only [smul_smul]
      congr 1
      ring
    _ = _ := laurent_shift_sum c (j.val : ℤ) (v j) s
      (fun m hm => hs (sub_mem_laurentProductFrequencies c hm j)) z

theorem laurentCirclePolynomial_smul_reverse_frequencies (c : ℤ →₀ ℂ)
    (v : Fin n → H) (z : AddCircle (1 : ℝ)) :
    laurentCirclePolynomial c z • reverseCirclePolynomial v z =
      ∑ q ∈ laurentProductFrequencies c n,
        fourier (T := (1 : ℝ)) q z • laurentProductCoefficient c v q :=
  laurentCirclePolynomial_smul_reverse c v _ (Finset.Subset.refl _) z

/-- A coefficient truncation can use the original product frequency
set, so finite Parseval compares two sums over exactly the same indices. -/
theorem laurentCirclePolynomial_filter_smul_reverse (c : ℤ →₀ ℂ)
    (v : Fin n → H) (p : ℤ → Prop) [DecidablePred p] (z : AddCircle (1 : ℝ)) :
    laurentCirclePolynomial (c.filter p) z • reverseCirclePolynomial v z =
      ∑ q ∈ laurentProductFrequencies c n,
        fourier (T := (1 : ℝ)) q z • laurentProductCoefficient (c.filter p) v q :=
  laurentCirclePolynomial_smul_reverse (c.filter p) v _
    (laurentProductFrequencies_filter_subset c n p) z

lemma laurentProductCoefficient_filter_nonnegative (c : ℤ →₀ ℂ)
    (v : Fin n → H) (q : ℤ) :
    laurentProductCoefficient (c.filter (fun m => 0 ≤ m)) v q =
      finiteSynthesis v (fun j => if 0 ≤ q + (j.val : ℤ) then c (q + (j.val : ℤ)) else 0) := rfl

end ProofProject
