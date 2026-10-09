import NLA.TR07.Reconstructible
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Simultaneous dependence vectors for centers sharing one reservoir. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace NLA.TR07

variable {ι κ δ ξ : Type*} [Fintype ι] [Fintype κ] [Fintype δ] [Fintype ξ]

private theorem norm_le_of_coordinates (e : κ ↪ ι)
    (x : EuclideanSpace ℝ κ) (y : EuclideanSpace ℝ ι) (h : ∀ j, y (e j) = x j) :
    ‖x‖ ≤ ‖y‖ := by
  have hs : ∑ i ∈ Finset.univ.map e, y i^2 ≤ ∑ i : ι, y i^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => sq_nonneg _)
  simp only [Finset.sum_map, h] at hs
  rw [← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq] at hs
  nlinarith [norm_nonneg x, norm_nonneg y]

/-- Every good center contributes a simultaneous dependence vector with its own identity row. -/
theorem defect_ge_half_reconstructible {k : ℕ} (a : κ ⊕ (δ ⊕ ξ) → Vec k)
    {η : ℝ} (hη : 0 < η) :
    (((Finset.univ : Finset κ).filter (fun i =>
      Reconstructible (a (Sum.inl i)) (fun j => a (Sum.inr (Sum.inl j))) (η/2))).card : ℝ) / 2 ≤
      defect a η := by
  let G := (Finset.univ : Finset κ).filter (fun i =>
    Reconstructible (a (Sum.inl i)) (fun j => a (Sum.inr (Sum.inl j))) (η/2))
  have hc (i : G) : ∃ c : δ → ℝ,
      ‖a (Sum.inl i.val) - ∑ j, c j • a (Sum.inr (Sum.inl j))‖ ≤ η/2 := by
    have hi := (Finset.mem_filter.mp i.property).2
    obtain ⟨y, hy, herror⟩ := hi
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hy
    exact ⟨c, by rwa [hc]⟩
  choose c hc using hc
  let w (j : G) : EuclideanSpace ℝ (κ ⊕ (δ ⊕ ξ)) := WithLp.toLp 2
    (Sum.elim (fun i => if j.val = i then 1 else 0)
      (Sum.elim (fun i => -c j i) (fun _ => 0)))
  let V := synthesis w
  have hV (x : EuclideanSpace ℝ G) : ‖x‖ ≤ ‖V x‖ := by
    let e : G ↪ κ ⊕ (δ ⊕ ξ) :=
      (Function.Embedding.subtype _).trans (Function.Embedding.inl)
    apply norm_le_of_coordinates e x (V x)
    intro j
    simp [V, synthesis, w, e]
  have hw (j : G) : synthesis a (V (EuclideanSpace.basisFun G ℝ j)) =
      a (Sum.inl j.val) - ∑ i, c j i • a (Sum.inr (Sum.inl i)) := by
    have hVj : V (EuclideanSpace.basisFun G ℝ j) = w j := by
      simp [V, synthesis]
    rw [hVj]
    simp [synthesis, w, Fintype.sum_sum_type, ← Finset.sum_neg_distrib, sub_eq_add_neg]
  have herror : ∑ j : G, ‖synthesis a (V (EuclideanSpace.basisFun G ℝ j))‖^2 ≤
      (Fintype.card G : ℝ) * η^2 / 4 := by
    calc
      _ ≤ ∑ _j : G, η^2/4 := by
        apply Finset.sum_le_sum
        intro j _
        rw [hw]
        have h := hc j
        have hn := norm_nonneg (a (Sum.inl j.val) - ∑ i, c j i • a (Sum.inr (Sum.inl i)))
        nlinarith
      _ = _ := by simp; ring
  have h := defect_ge_half_of_witnesses a hη V hV herror
  simpa only [Fintype.card_coe] using h

end NLA.TR07
