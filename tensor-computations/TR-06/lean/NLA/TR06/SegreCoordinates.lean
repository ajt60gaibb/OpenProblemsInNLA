/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original TR-06 mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.SegreBoundary
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.TR06.Segre
variable {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

theorem card_coordinate (q₀ : Fin r → TensorIndex d n) :
    Fintype.card (Coordinate q₀) = expectedDimension d n r := by
  simp only [Coordinate, Fintype.card_sigma, Fintype.card_option]
  have hcard (i : Fin r) (j : Fin d) :
      Fintype.card {u : Fin (n j) // u ≠ q₀ i j} = n j - 1 := by
    rw [Fintype.card_subtype_compl]
    simp
  simp_rw [hcard]
  simp [expectedDimension, Nat.add_comm]

theorem dimension_statement : DimensionStatement := by
  intro d n r q₀
  refine ⟨card_coordinate q₀, ?_, ?_⟩
  · change Module.finrank ℝ (EuclideanSpace ℝ (Coordinate q₀)) = _
    rw [finrank_euclideanSpace]
    exact card_coordinate q₀
  · change Module.finrank ℂ (EuclideanSpace ℂ (Coordinate q₀)) = _
    rw [finrank_euclideanSpace]
    exact card_coordinate q₀

@[simp] theorem eval_factorPolynomial (q₀ : Fin r → TensorIndex d n)
    (z : Parameter 𝕜 q₀) (i : Fin r) (j : Fin d) (u : Fin (n j)) :
    MvPolynomial.eval (fun c => z c) (factorPolynomial 𝕜 q₀ i j u) = factor q₀ z i j u := by
  simp only [factorPolynomial, factor]
  split_ifs <;> simp

@[simp] theorem eval_summandPolynomial (q₀ : Fin r → TensorIndex d n)
    (z : Parameter 𝕜 q₀) (i : Fin r) (q : TensorIndex d n) :
    MvPolynomial.eval (fun c => z c) (summandPolynomial 𝕜 q₀ i q) = summands q₀ z i q := by
  simp [summandPolynomial, summands, pureTensor]

@[simp] theorem eval_sumPolynomial (q₀ : Fin r → TensorIndex d n)
    (z : Parameter 𝕜 q₀) (q : TensorIndex d n) :
    MvPolynomial.eval (fun c => z c) (sumPolynomial 𝕜 q₀ q) = sum q₀ z q := by
  simp [sumPolynomial, sum]

@[simp] theorem eval_pullback (q₀ : Fin r → TensorIndex d n)
    (z : Parameter 𝕜 q₀) (p : MvPolynomial (TensorIndex d n) 𝕜) :
    MvPolynomial.eval (fun c => z c) (pullback q₀ p) =
      MvPolynomial.eval (fun q => sum q₀ z q) p := by
  change MvPolynomial.eval₂Hom (RingHom.id 𝕜) (fun c => z c)
    (MvPolynomial.bind₁ (sumPolynomial 𝕜 q₀) p) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval (fun q => MvPolynomial.eval (fun c => z c)
    (sumPolynomial 𝕜 q₀ q)) p = _
  simp only [eval_sumPolynomial]

theorem evaluation_statement : EvaluationStatement := by
  intro 𝕜 _ d n r q₀ z
  exact ⟨eval_summandPolynomial q₀ z, eval_sumPolynomial q₀ z, eval_pullback q₀ z⟩

@[simp] theorem factor_pivot (q₀ : Fin r → TensorIndex d n)
    (z : Parameter 𝕜 q₀) (i : Fin r) (j : Fin d) : factor q₀ z i j (q₀ i j) = 1 := by
  simp [factor]

@[simp] theorem summands_pivot (q₀ : Fin r → TensorIndex d n)
    (z : Parameter 𝕜 q₀) (i : Fin r) : summands q₀ z i (q₀ i) = z ⟨i, none⟩ := by
  simp [summands, pureTensor]

/-- An amplitude is absorbed into one actual tensor factor. -/
theorem pureTensor_smul_mode (u : (j : Fin d) → Fin (n j) → 𝕜)
    (j₀ : Fin d) (t : 𝕜) :
    pureTensor (Function.update u j₀ (fun v => t * u j₀ v)) = t • pureTensor u := by
  ext q
  change (∏ j, (Function.update u j₀ (fun v => t * u j₀ v)) j (q j)) =
    t * ∏ j, u j (q j)
  calc
    _ = ∏ j, (if j = j₀ then t else 1) * u j (q j) := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases h : j = j₀
      · subst j; simp
      · simp [h]
    _ = t * ∏ j, u j (q j) := by rw [Finset.prod_mul_distrib]; simp

theorem decomposes_decoded (hd : 0 < d) (q₀ : Fin r → TensorIndex d n)
    (z : Parameter 𝕜 q₀) (hz : ∀ i, z ⟨i, none⟩ ≠ 0) :
    Decomposes (summands q₀ z) (sum q₀ z) := by
  refine ⟨fun i => ⟨?_, ?_⟩, rfl⟩
  · intro h
    have hval := congrArg (fun A : Tensor 𝕜 d n => A (q₀ i)) h
    exact hz i (by simpa using hval)
  · refine ⟨Function.update (factor q₀ z i) ⟨0, hd⟩
      (fun v => z ⟨i, none⟩ * factor q₀ z i ⟨0, hd⟩ v), ?_⟩
    exact pureTensor_smul_mode (factor q₀ z i) ⟨0, hd⟩ (z ⟨i, none⟩)

theorem decomposition_statement : DecompositionStatement := by
  intro 𝕜 _ d n r hd q₀ z hz
  exact ⟨decomposes_decoded hd q₀ z hz, summands_pivot q₀ z⟩

/-- Normalize chosen actual tensor factors at the prescribed nonzero pivots.
No positive-mode assumption is needed for this representation direction. -/
theorem represented_of_nonzero_pivots (q₀ : Fin r → TensorIndex d n)
    (a : Fin r → Tensor 𝕜 d n) (ha : ∀ i, RankOne (a i))
    (hpivot : ∀ i, a i (q₀ i) ≠ 0) :
    ∃ z : Parameter 𝕜 q₀, (∀ i, z ⟨i, none⟩ ≠ 0) ∧ summands q₀ z = a := by
  classical
  choose u hu using fun i => (ha i).2
  have hp (i : Fin r) : pureTensor (u i) (q₀ i) ≠ 0 := by rw [hu]; exact hpivot i
  have hdenom (i : Fin r) (j : Fin d) : u i j (q₀ i j) ≠ 0 := by
    have hi := hp i
    change (∏ k, u i k (q₀ i k)) ≠ 0 at hi
    exact (Finset.prod_ne_zero_iff.mp hi) j (Finset.mem_univ j)
  let z : Parameter 𝕜 q₀ := WithLp.toLp 2 (fun t =>
    t.2.elim (a t.1 (q₀ t.1)) (fun v => u t.1 v.1 v.2.val / u t.1 v.1 (q₀ t.1 v.1)))
  have hzfactor (i : Fin r) (j : Fin d) (v : Fin (n j)) :
      factor q₀ z i j v = u i j v / u i j (q₀ i j) := by
    by_cases h : v = q₀ i j
    · subst v; simp [factor, hdenom]
    · simp [factor, h, z]
  refine ⟨z, hpivot, ?_⟩
  funext i
  ext q
  change a i (q₀ i) * (∏ j, factor q₀ z i j (q j)) = a i q
  simp_rw [hzfactor]
  rw [← hu i]
  change (∏ j, u i j (q₀ i j)) * (∏ j, u i j (q j) / u i j (q₀ i j)) =
    ∏ j, u i j (q j)
  rw [Finset.prod_div_distrib]
  exact mul_div_cancel₀ _ (hp i)

theorem representation_statement : RepresentationStatement := by
  intro 𝕜 _ d n r q₀ a ha hpivot
  exact represented_of_nonzero_pivots q₀ a ha hpivot

#print axioms dimension_statement
#print axioms evaluation_statement
#print axioms decomposition_statement
#assert_trust kernel dimension_statement
#assert_trust kernel evaluation_statement
#assert_trust kernel decomposition_statement
#print axioms representation_statement
#assert_trust kernel representation_statement
end NLA.TR06.Segre
