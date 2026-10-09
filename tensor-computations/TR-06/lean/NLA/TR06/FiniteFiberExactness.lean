/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original TR-06 mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.FiniteFiberExactnessBoundary
import NLA.TR06.SegreCoordinates
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open Set
namespace NLA.TR06.FiniteFiber
variable {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} {n : Fin d → ℕ} {r m : ℕ}

theorem rank_bound_statement : RankBoundStatement := by
  intro 𝕜 _ d n r A ⟨a, ha⟩
  obtain ⟨m, hm, _, b, hb⟩ := exists_decomposes_remove_zeros a ha.1
  exact ⟨m, hm, b, ha.2 ▸ hb⟩

/-- Scalar absorption uses an actual mode; zero scalar values are retained. -/
theorem rankAtMostOne_smul (hd : 0 < d) {B : Tensor 𝕜 d n} (hB : RankOne B) (t : 𝕜) :
    rankAtMostOne (t • B) := by
  by_cases h : t • B = 0
  · exact Or.inl h
  · obtain ⟨u, hu⟩ := hB.2
    refine Or.inr ⟨h, Function.update u ⟨0, hd⟩ (fun v => t * u ⟨0, hd⟩ v), ?_⟩
    rw [Segre.pureTensor_smul_mode, hu]

theorem unit_tensor_statement : UnitTensorStatement := by
  intro 𝕜 _ d n hn
  refine ⟨?_, (fun _ _ => 1), rfl⟩
  intro h
  have he := congrArg (fun A : Tensor 𝕜 d n => A (fun j => ⟨0, hn j⟩)) h
  simp [unitTensor, pureTensor] at he

theorem splitTuple_injective (hm : 0 < m) (hmr : m < r)
    (a : Fin m → Tensor 𝕜 d n) (ha : RankOne (a ⟨0, hm⟩)) :
    Function.Injective (splitTuple (r := r) hm a) := by
  intro s t hst
  have hr : 0 < r := lt_trans hm hmr
  have he := congrArg (fun b : Fin r → Tensor 𝕜 d n => b ⟨0, hr⟩) hst
  have he' : s • a ⟨0, hm⟩ = t • a ⟨0, hm⟩ := by simpa [splitTuple] using he
  exact (smul_left_injective 𝕜 ha.1) he'

theorem sum_splitTuple (hm : 0 < m) (hmr : m < r)
    (a : Fin m → Tensor 𝕜 d n) (t : 𝕜) :
    ∑ i : Fin r, splitTuple hm a t i = ∑ i : Fin m, a i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hmr)
  rw [Fin.sum_univ_add]
  have htail : (∑ i : Fin k, splitTuple hm a t (Fin.natAdd (m + 2) i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [splitTuple, Fin.val_natAdd]
    split_ifs <;> try omega
    rfl
  rw [htail, add_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hhead : splitTuple hm a t (Fin.castAdd k (0 : Fin (m + 2))) = t • a 0 := by simp [splitTuple]
  have hnext : splitTuple hm a t (Fin.castAdd k (Fin.succ (0 : Fin (m + 1)))) = (1 - t) • a 0 := by
    simp [splitTuple]
  rw [hhead, hnext]
  have hrest : (∑ i : Fin m, splitTuple hm a t (Fin.castAdd k i.succ.succ)) =
      ∑ i : Fin m, a i.succ := by
    apply Finset.sum_congr rfl
    intro i _
    simp [splitTuple, show i.val + 1 < m + 1 by omega]
    rfl
  rw [hrest, ← add_assoc, ← add_smul, show t + (1 - t) = 1 by ring, one_smul,
    Fin.sum_univ_succ]


theorem split_family_statement : SplitFamilyStatement := by
  intro 𝕜 _ d n r m hd hm hmr A a ha
  refine ⟨splitTuple_injective hm hmr a (ha.1 _), fun t => ?_⟩
  refine ⟨fun i => ?_, (sum_splitTuple hm hmr a t).trans ha.2⟩
  simp only [splitTuple]
  split_ifs
  · exact rankAtMostOne_smul hd (ha.1 _) t
  · exact rankAtMostOne_smul hd (ha.1 _) (1 - t)
  · exact Or.inr (ha.1 _)
  · exact Or.inl rfl

theorem cancelTuple_injective (hr : 2 ≤ r) (B : Tensor 𝕜 d n) (hB : B ≠ 0) :
    Function.Injective (cancelTuple (r := r) B) := by
  intro s t hst
  have hr0 : 0 < r := by omega
  have he := congrArg (fun b : Fin r → Tensor 𝕜 d n => b ⟨0, hr0⟩) hst
  have he' : s • B = t • B := by simpa [cancelTuple] using he
  exact (smul_left_injective 𝕜 hB) he'

theorem sum_cancelTuple (hr : 2 ≤ r) (B : Tensor 𝕜 d n) (t : 𝕜) :
    ∑ i : Fin r, cancelTuple B t i = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [Fin.sum_univ_add]
  have htail : (∑ i : Fin k, cancelTuple B t (Fin.natAdd 2 i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [cancelTuple, show ¬ 2 + i.val = 1 by omega]
  rw [htail, add_zero]
  simp [Fin.sum_univ_succ, cancelTuple]

theorem cancel_family_statement : CancelFamilyStatement := by
  intro 𝕜 _ d n r hd hr B hB
  refine ⟨cancelTuple_injective hr B hB.1, fun t => ?_⟩
  refine ⟨fun i => ?_, sum_cancelTuple hr B t⟩
  simp only [cancelTuple]
  split_ifs
  · exact rankAtMostOne_smul hd hB t
  · simpa only [neg_smul] using rankAtMostOne_smul hd hB (-t)
  · exact Or.inl rfl

theorem shorter_infinite_statement : ShorterInfiniteStatement := by
  intro 𝕜 _ d n r hd hn hr A m hmr ⟨a, ha⟩
  by_cases hm : 0 < m
  · obtain ⟨hinj, hmem⟩ := split_family_statement 𝕜 d n r m hd hm hmr A a ha
    exact (Set.infinite_range_of_injective hinj).mono (by
      rintro _ ⟨t, rfl⟩
      exact hmem t)
  · have hm0 : m = 0 := by omega
    subst m
    have hA : A = 0 := by simpa using ha.2.symm
    subst A
    obtain ⟨hinj, hmem⟩ := cancel_family_statement 𝕜 d n r hd hr
      (unitTensor 𝕜 d n) (unit_tensor_statement 𝕜 d n hn)
    exact (Set.infinite_range_of_injective hinj).mono (by
      rintro _ ⟨t, rfl⟩
      exact hmem t)

theorem exact_rank_statement : ExactRankStatement := by
  intro 𝕜 _ d n r hd hn hr A hfinite hnonempty
  obtain ⟨m, hm, a, ha⟩ := rank_bound_statement 𝕜 d n r A hnonempty
  have hnotlt : ¬ m < r := by
    intro hlt
    exact hfinite.not_infinite (shorter_infinite_statement 𝕜 d n r hd hn hr A m hlt ⟨a, ha⟩)
  have heq : m = r := by omega
  subst m
  refine ⟨⟨a, ha⟩, fun m hmr hdec => ?_⟩
  exact hfinite.not_infinite (shorter_infinite_statement 𝕜 d n r hd hn hr A m hmr hdec)

#print axioms rank_bound_statement
#print axioms split_family_statement
#print axioms unit_tensor_statement
#print axioms cancel_family_statement
#print axioms shorter_infinite_statement
#print axioms exact_rank_statement
#assert_trust kernel rank_bound_statement
#assert_trust kernel split_family_statement
#assert_trust kernel unit_tensor_statement
#assert_trust kernel cancel_family_statement
#assert_trust kernel shorter_infinite_statement
#assert_trust kernel exact_rank_statement
end NLA.TR06.FiniteFiber
