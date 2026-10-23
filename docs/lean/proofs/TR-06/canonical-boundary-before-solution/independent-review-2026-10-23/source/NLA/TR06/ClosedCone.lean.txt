/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original TR-06 mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.ClosedFibers
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open Set
namespace NLA.TR06

variable {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} {n : Fin d → ℕ}

/-- A genuine homogeneous polynomial expression of degree at most d for positive d. The whole
finite family ranges over all tensor pivot/target coordinate pairs. -/
def rankOnePivotPolynomial (𝕜 : Type*) [RCLike 𝕜] {d : ℕ} {n : Fin d → ℕ}
    (p q : TensorIndex d n) : MvPolynomial (TensorIndex d n) 𝕜 :=
  MvPolynomial.X q * MvPolynomial.X p ^ (d - 1) -
    ∏ j : Fin d, MvPolynomial.X (Function.update p j (q j))

/-- Finite diagonal product identity in an arbitrary commutative monoid.
It uses no cancellation and therefore applies inside raw factor polynomial rings. -/
theorem prod_prod_diagonal_identity {M ι : Type*} [CommMonoid M] [Fintype ι] [DecidableEq ι]
    (a b : ι → M) :
    (∏ i, a i) * (∏ i, b i) ^ (Fintype.card ι - 1) =
      ∏ j, ∏ i, if i = j then a i else b i := by
  classical
  rw [Finset.prod_comm]
  symm
  calc
    (∏ i, ∏ j, if i = j then a i else b i) =
        ∏ i, a i * b i ^ (Fintype.card ι - 1) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
      simp only [if_true]
      congr 1
      calc
        (∏ j ∈ Finset.univ \ {i}, if i = j then a i else b i) =
            ∏ _j ∈ (Finset.univ \ {i} : Finset ι), b i := by
          apply Finset.prod_congr rfl
          intro j hj
          have hne : i ≠ j := by
            intro h
            exact (Finset.mem_sdiff.mp hj).2 (by simp [← h])
          simp [hne]
        _ = b i ^ (Fintype.card ι - 1) := by
          simp [Finset.card_sdiff]
    _ = (∏ i, a i) * (∏ i, b i) ^ (Fintype.card ι - 1) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow]

/-- Every pivot equation holds for every pure tensor, even at a zero pivot. -/
theorem pureTensor_pivot_identity (_hd : 0 < d)
    (u : (j : Fin d) → Fin (n j) → 𝕜) (p q : TensorIndex d n) :
    pureTensor u q * pureTensor u p ^ (d - 1) =
      ∏ j : Fin d, pureTensor u (Function.update p j (q j)) := by
  change (∏ i, u i (q i)) * (∏ i, u i (p i)) ^ (d - 1) =
    ∏ j, ∏ i, u i ((Function.update p j (q j)) i)
  have hprod := prod_prod_diagonal_identity (fun i : Fin d => u i (q i))
    (fun i : Fin d => u i (p i))
  simp only [Fintype.card_fin] at hprod
  rw [hprod]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : i = j
  · subst i
    simp
  · simp [h]

/-- Normalized coordinate slices of an actual tensor at a fixed pivot. -/
def rankOneNormalizedFactors (p : TensorIndex d n) (A : Tensor 𝕜 d n)
    (j : Fin d) (i : Fin (n j)) : 𝕜 := A (Function.update p j i) / A p

/-- The pivot identities reconstruct the original tensor whenever the chosen
pivot is actually nonzero; only this converse step uses division. -/
theorem reconstruction_of_pivot_equations (hd : 0 < d) (A : Tensor 𝕜 d n)
    (p : TensorIndex d n) (hp : A p ≠ 0)
    (heq : ∀ q : TensorIndex d n,
      A q * A p ^ (d - 1) = ∏ j : Fin d, A (Function.update p j (q j))) :
    A = A p • pureTensor (rankOneNormalizedFactors p A) := by
  ext q
  change A q = A p * ∏ j, A (Function.update p j (q j)) / A p
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← heq q]
  have hpow : A p ^ d = A p ^ (d - 1) * A p := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow]
  field_simp

private theorem pureTensor_absorb_scale
    (u : (j : Fin d) → Fin (n j) → 𝕜) (j₀ : Fin d) (t : 𝕜) :
    pureTensor (Function.update u j₀ (t • u j₀)) = t • pureTensor u := by
  ext q
  change (∏ j, Function.update u j₀ (t • u j₀) j (q j)) = t * ∏ j, u j (q j)
  calc
    (∏ j, Function.update u j₀ (t • u j₀) j (q j)) =
        ∏ j, (if j = j₀ then t else 1) * u j (q j) := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases h : j = j₀
      · subst j
        simp
      · simp [h]
    _ = t * ∏ j, u j (q j) := by rw [Finset.prod_mul_distrib]; simp

/-- Zero or actual nonzero rank one is equivalent to every pivot equation. -/
theorem rankAtMostOne_iff_pivot_equations (hd : 0 < d) (A : Tensor 𝕜 d n) :
    rankAtMostOne A ↔ ∀ p q : TensorIndex d n,
      A q * A p ^ (d - 1) = ∏ j : Fin d, A (Function.update p j (q j)) := by
  constructor
  · rintro (rfl | ⟨_, u, rfl⟩) p q
    · simp [hd.ne']
    · exact pureTensor_pivot_identity hd u p q
  · intro h
    by_cases hA : A = 0
    · exact Or.inl hA
    · have hex : ∃ p : TensorIndex d n, A p ≠ 0 := by
        by_contra hn
        push Not at hn
        apply hA
        ext q
        exact hn q
      obtain ⟨p, hp⟩ := hex
      let j₀ : Fin d := ⟨0, hd⟩
      refine Or.inr ⟨hA, Function.update (rankOneNormalizedFactors p A) j₀
        (A p • rankOneNormalizedFactors p A j₀), ?_⟩
      exact (pureTensor_absorb_scale _ j₀ (A p)).trans
        (reconstruction_of_pivot_equations hd A p hp (h p)).symm

/-- The actual closed cone is the common zero locus of a genuine finite
family of coordinate polynomials. No assertion about their generated ideal is made. -/
theorem rankAtMostOne_iff_eval_pivotPolynomial_eq_zero (hd : 0 < d) (A : Tensor 𝕜 d n) :
    rankAtMostOne A ↔ ∀ p q : TensorIndex d n,
      MvPolynomial.eval (fun v => A v) (rankOnePivotPolynomial 𝕜 p q) = 0 := by
  rw [rankAtMostOne_iff_pivot_equations hd A]
  simp [rankOnePivotPolynomial, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
    sub_eq_zero]

/-- Exact generic-scalar pivot reconstruction from actual rank-one status. -/
theorem rankOne_reconstruction_rlike (hd : 0 < d) (A : Tensor 𝕜 d n)
    (hA : RankOne A) (p : TensorIndex d n) (hp : A p ≠ 0) :
    A = A p • pureTensor (rankOneNormalizedFactors p A) :=
  reconstruction_of_pivot_equations hd A p hp
    ((rankAtMostOne_iff_pivot_equations hd A).mp (Or.inr hA) p)

/-- The raw factor parametrization has exactly the zero-inclusive cone as range. -/
theorem range_pureTensor_eq_rankAtMostOne (hd : 0 < d) :
    Set.range (pureTensor : ((j : Fin d) → Fin (n j) → 𝕜) → Tensor 𝕜 d n) =
      {A : Tensor 𝕜 d n | rankAtMostOne A} := by
  ext A
  constructor
  · rintro ⟨u, rfl⟩
    by_cases h : pureTensor u = 0
    · exact Or.inl h
    · exact Or.inr ⟨h, u, rfl⟩
  · rintro (rfl | ⟨_, u, hu⟩)
    · refine ⟨fun _ _ => 0, ?_⟩
      ext q
      simp [pureTensor, hd.ne']
    · exact ⟨u, hu⟩

/-- Closedness of the actual cone follows from the proved polynomial zero locus. -/
theorem isClosed_rankAtMostOne (hd : 0 < d) :
    IsClosed {A : Tensor 𝕜 d n | rankAtMostOne A} := by
  have heq : {A : Tensor 𝕜 d n | rankAtMostOne A} =
      ⋂ p, ⋂ q, {A | MvPolynomial.eval (fun v => A v) (rankOnePivotPolynomial 𝕜 p q) = 0} := by
    ext A
    simp only [mem_iInter, mem_ofPred_eq]
    exact rankAtMostOne_iff_eval_pivotPolynomial_eq_zero hd A
  rw [heq]
  apply isClosed_iInter
  intro p
  apply isClosed_iInter
  intro q
  exact isClosed_eq ((MvPolynomial.continuous_eval _).comp (PiLp.continuous_ofLp 2 _))
    continuous_const

/-- Closedness of the full tensor product, including zero entries and r=0. -/
theorem isClosed_closedRankOneProduct (hd : 0 < d) (r : ℕ) :
    IsClosed (closedRankOneProduct 𝕜 d n r) := by
  change IsClosed {a : Fin r → Tensor 𝕜 d n | ∀ i, rankAtMostOne (a i)}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro i
  change IsClosed ((fun a : Fin r → Tensor 𝕜 d n => a i) ⁻¹'
    {A : Tensor 𝕜 d n | rankAtMostOne A})
  exact (isClosed_rankAtMostOne (𝕜 := 𝕜) (n := n) hd).preimage
    (continuous_apply i : Continuous (fun a : Fin r → Tensor 𝕜 d n => a i))

/-- Closedness of the entire addition fiber, without rank or uniqueness premises. -/
theorem isClosed_closedAdditionFiber (hd : 0 < d) (r : ℕ) (A : Tensor 𝕜 d n) :
    IsClosed (closedAdditionFiber r A) := by
  change IsClosed (closedRankOneProduct 𝕜 d n r ∩ {a | ∑ i, a i = A})
  exact (isClosed_closedRankOneProduct hd r).inter
    (isClosed_eq (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const)

#print axioms prod_prod_diagonal_identity
#print axioms pureTensor_pivot_identity
#print axioms reconstruction_of_pivot_equations
#print axioms rankAtMostOne_iff_pivot_equations
#print axioms rankAtMostOne_iff_eval_pivotPolynomial_eq_zero
#print axioms rankOne_reconstruction_rlike
#print axioms range_pureTensor_eq_rankAtMostOne
#print axioms isClosed_rankAtMostOne
#print axioms isClosed_closedRankOneProduct
#print axioms isClosed_closedAdditionFiber
#assert_trust kernel prod_prod_diagonal_identity
#assert_trust kernel pureTensor_pivot_identity
#assert_trust kernel reconstruction_of_pivot_equations
#assert_trust kernel rankAtMostOne_iff_pivot_equations
#assert_trust kernel rankAtMostOne_iff_eval_pivotPolynomial_eq_zero
#assert_trust kernel rankOne_reconstruction_rlike
#assert_trust kernel range_pureTensor_eq_rankAtMostOne
#assert_trust kernel isClosed_rankAtMostOne
#assert_trust kernel isClosed_closedRankOneProduct
#assert_trust kernel isClosed_closedAdditionFiber
end NLA.TR06
