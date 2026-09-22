/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical counterexample: Matthew J. Colbrook.
AI-assisted rank proof following the independently reviewed statement freeze.
-/
import NLA.TR27.Independence
import NLA.TR27.Geometry
import Mathlib.LinearAlgebra.Basis.VectorSpace

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct LinearAlgebra.Projectivization
namespace NLA.TR27

/-- A zero cone vector is allowed and is absorbed in a zero scalar. -/
theorem cone_vector_parameter (v : Space) (hv : v ∈ witnessVariety.cone) :
    ∃ (a : ℂ) (t : Option ℂ), v = a • curve t := by
  rw [whole_closed_image.2] at hv
  rcases hv with rfl | ⟨a, _, t, ht⟩
  · exact ⟨0, some 0, by simp⟩
  · exact ⟨a, t, ht⟩

theorem curve_linearIndepOn (s : Finset (Option ℂ)) (hs : s.card ≤ 8) :
    LinearIndepOn ℂ curve (s : Set (Option ℂ)) := by
  classical
  change LinearIndependent ℂ (fun x : s => curve x)
  let e := Fintype.equivFin s
  have hli := projected_curve_independent (by simpa using hs : Fintype.card s ≤ 8)
    (fun i => (e.symm i : Option ℂ)) (Subtype.val_injective.comp e.symm.injective)
  simpa only [Function.comp_def, Equiv.symm_apply_apply] using hli.comp e e.injective

/-- A coordinate on a finite independent family extends to the ambient space. -/
theorem independent_dual {ι : Type*} [DecidableEq ι] (v : ι → Space) (hv : LinearIndependent ℂ v)
    (i : ι) : ∃ f : Space →ₗ[ℂ] ℂ, ∀ j, f (v j) = if j = i then 1 else 0 := by
  classical
  let l : Submodule.span ℂ (Set.range v) →ₗ[ℂ] ℂ := (Finsupp.lapply i).comp hv.repr
  obtain ⟨f, hf⟩ := l.exists_extend
  refine ⟨f, ?_⟩
  intro j
  let x : Submodule.span ℂ (Set.range v) := ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩
  have hfx := congrArg (fun g : Submodule.span ℂ (Set.range v) →ₗ[ℂ] ℂ => g x) hf
  change f (v j) = (hv.repr x) i at hfx
  rw [hfx, hv.repr_eq_single j x rfl]
  simp [Finsupp.single_apply]

theorem curve_dual (s : Finset (Option ℂ)) (hs : s.card ≤ 8)
    (r : Option ℂ) (hr : r ∈ s) :
    ∃ f : Space →ₗ[ℂ] ℂ, ∀ t ∈ s, f (curve t) = if t = r then 1 else 0 := by
  classical
  obtain ⟨f, hf⟩ := independent_dual (fun t : s => curve t) (curve_linearIndepOn s hs) ⟨r, hr⟩
  refine ⟨f, ?_⟩
  intro t ht
  simpa only [Subtype.mk.injEq] using hf ⟨t, ht⟩

theorem witness_rank_at_most_three : ConeRankAtMost witnessVariety.cone 3 witnessVector := by
  refine ⟨3, le_rfl, fun _ => 1, ![curve (some 1), curve (some 2), curve (some 3)], ?_, ?_⟩
  · intro i
    fin_cases i <;> exact curve_mem_cone _
  · simpa [Fin.sum_univ_succ, add_assoc] using curve_three_sum.symm

theorem witness_not_rank_two : ¬ ConeRankAtMost witnessVariety.cone 2 witnessVector := by
  classical
  rintro ⟨k, hk, a, x, hx, hsum⟩
  choose b t ht using fun i => cone_vector_parameter (x i) (hx i)
  have hparam : witnessVector = ∑ i, (a i * b i) • curve (t i) := by
    rw [hsum]
    apply Finset.sum_congr rfl
    intro i _
    rw [ht i, smul_smul]
  let s₀ : Finset (Option ℂ) := {some 1, some 2, some 3}
  let q : Finset (Option ℂ) := Finset.univ.image t
  have hq : q.card ≤ 2 := (Finset.card_image_le).trans (by simpa using hk)
  have hthree : s₀.card = 3 := by norm_num [s₀]
  have hnot : ¬ s₀ ⊆ q := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨r, hr, hrq⟩ := Finset.not_subset.mp hnot
  let s := s₀ ∪ q
  have hs : s.card ≤ 8 := by
    have := Finset.card_union_le s₀ q
    dsimp [s]
    omega
  obtain ⟨f, hf⟩ := curve_dual s hs r (Finset.mem_union_left q hr)
  have hf1 : f witnessVector = 1 := by
    rw [← curve_three_sum, map_add, map_add,
      hf (some 1) (by simp [s, s₀]), hf (some 2) (by simp [s, s₀]),
      hf (some 3) (by simp [s, s₀])]
    simp only [s₀, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl <;> norm_num
  have hf0 : f witnessVector = 0 := by
    rw [hparam, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    have hti : t i ∈ q := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hne : t i ≠ r := by intro he; exact hrq (he ▸ hti)
    rw [map_smul, hf (t i) (Finset.mem_union_right s₀ hti), if_neg hne, smul_zero]
  exact one_ne_zero (hf1.symm.trans hf0)

theorem witness_three_terms :
    witnessVector ≠ 0 ∧
    curve (some 1) + curve (some 2) + curve (some 3) = witnessVector ∧
    ConeRankAtMost witnessVariety.cone 3 witnessVector ∧
    ¬ ConeRankAtMost witnessVariety.cone 2 witnessVector := by
  exact ⟨witnessVector_nonzero, curve_three_sum, witness_rank_at_most_three,
    witness_not_rank_two⟩

theorem curve_three_sum_fin :
    (∑ i : Fin 3, curve (some ((i : ℕ) + 1 : ℂ))) = witnessVector := by
  norm_num [Fin.sum_univ_succ]
  simpa [add_assoc] using curve_three_sum

theorem square_nine_identity :
    witnessVector ⊗ₜ[ℂ] witnessVector =
      ∑ i : Fin 3, ∑ j : Fin 3,
        curve (some ((i : ℕ) + 1 : ℂ)) ⊗ₜ[ℂ] curve (some ((j : ℕ) + 1 : ℂ)) := by
  conv_lhs => rw [← curve_three_sum_fin]
  rw [TensorProduct.sum_tmul]
  simp only [TensorProduct.tmul_sum]

theorem square_nine_terms :
    witnessVector ⊗ₜ[ℂ] witnessVector =
      ∑ i : Fin 3, ∑ j : Fin 3,
        curve (some ((i : ℕ) + 1 : ℂ)) ⊗ₜ[ℂ] curve (some ((j : ℕ) + 1 : ℂ)) ∧
    TensorRankAtMost witnessVariety.cone 9 (witnessVector ⊗ₜ[ℂ] witnessVector) := by
  refine ⟨square_nine_identity, ?_⟩
  let e : Fin 9 ≃ Fin 3 × Fin 3 := (@finProdFinEquiv 3 3).symm
  refine ⟨9, le_rfl, fun _ => 1,
    (fun i => curve (some (((e i).1 : ℕ) + 1 : ℂ))),
    (fun i => curve (some (((e i).2 : ℕ) + 1 : ℂ))), ?_, ?_⟩
  · intro i
    exact ⟨curve_mem_cone _, curve_mem_cone _⟩
  · simp only [one_smul]
    rw [square_nine_identity]
    exact ((e.sum_comp (fun ij =>
      curve (some ((ij.1 : ℕ) + 1 : ℂ)) ⊗ₜ[ℂ] curve (some ((ij.2 : ℕ) + 1 : ℂ)))).trans
      (Fintype.sum_prod_type _)).symm

/-- Any finite curve expansion of the target has at least three nonzero weights. -/
theorem witness_expansion_support (s : Finset (Option ℂ)) (a : s → ℂ)
    (ha : witnessVector = ∑ i : s, a i • curve i) :
    3 ≤ (Finset.univ.filter (fun i : s => a i ≠ 0)).card := by
  classical
  by_contra h
  let q : Finset s := Finset.univ.filter (fun i : s => a i ≠ 0)
  have hq : q.card ≤ 2 := by
    change (Finset.univ.filter (fun i : s => a i ≠ 0)).card ≤ 2
    omega
  let e := (Fintype.equivFin q).symm
  apply witness_not_rank_two
  refine ⟨Fintype.card q, by simpa using hq,
    (fun i => a (e i)), (fun i => curve (e i).val), ?_, ?_⟩
  · intro i
    exact curve_mem_cone _
  · rw [ha, e.sum_comp (fun i : q => a i • curve i.val)]
    rw [q.sum_coe_sort (fun i : s => a i • curve i)]
    dsimp [q]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : a i = 0 <;> simp [hi]

def witnessDual : Space →ₗ[ℂ] ℂ := (-1 / 3 : ℂ) • LinearMap.proj 0

theorem witnessDual_value : witnessDual witnessVector = 1 := by
  norm_num [witnessDual, witnessVector_apply, coordinateIndex, powerSum]

def contractRight : (Space ⊗[ℂ] Space) →ₗ[ℂ] Space :=
  (TensorProduct.rid ℂ Space).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : Space →ₗ[ℂ] Space) witnessDual)

def contractLeft : (Space ⊗[ℂ] Space) →ₗ[ℂ] Space :=
  (TensorProduct.lid ℂ Space).toLinearMap.comp
    (TensorProduct.map witnessDual (LinearMap.id : Space →ₗ[ℂ] Space))

theorem contractRight_tmul (x y : Space) :
    contractRight (x ⊗ₜ[ℂ] y) = witnessDual y • x := by
  simp [contractRight]

theorem contractLeft_tmul (x y : Space) :
    contractLeft (x ⊗ₜ[ℂ] y) = witnessDual x • y := by
  simp [contractLeft]

def pairDual (f g : Space →ₗ[ℂ] ℂ) : (Space ⊗[ℂ] Space) →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp (TensorProduct.map f g)

theorem pairDual_tmul (f g : Space →ₗ[ℂ] ℂ) (x y : Space) :
    pairDual f g (x ⊗ₜ[ℂ] y) = f x * g y := by
  simp [pairDual, smul_eq_mul]

theorem cone_square_parameters {k : ℕ} (a : Fin k → ℂ) (x y : Fin k → Space)
    (hx : ∀ i, x i ∈ witnessVariety.cone) (hy : ∀ i, y i ∈ witnessVariety.cone) :
    ∃ (d : Fin k → ℂ) (t u : Fin k → Option ℂ),
      (∑ i, a i • (x i ⊗ₜ[ℂ] y i)) =
        ∑ i, d i • (curve (t i) ⊗ₜ[ℂ] curve (u i)) := by
  choose b t ht using fun i => cone_vector_parameter (x i) (hx i)
  choose c u hu using fun i => cone_vector_parameter (y i) (hy i)
  refine ⟨fun i => a i * (b i * c i), t, u, ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  rw [ht i, hu i, TensorProduct.smul_tmul_smul, smul_smul]

theorem square_parameter_lower_bound {k : ℕ} (hk : k ≤ 8) (d : Fin k → ℂ)
    (t u : Fin k → Option ℂ)
    (h : witnessVector ⊗ₜ[ℂ] witnessVector =
      ∑ i, d i • (curve (t i) ⊗ₜ[ℂ] curve (u i))) : False := by
  classical
  let L : Finset (Option ℂ) := Finset.univ.image t
  let R : Finset (Option ℂ) := Finset.univ.image u
  have hL : L.card ≤ 8 := (Finset.card_image_le).trans (by simpa using hk)
  have hR : R.card ≤ 8 := (Finset.card_image_le).trans (by simpa using hk)
  have ht (i : Fin k) : t i ∈ L := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hu (i : Fin k) : u i ∈ R := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hvL : witnessVector ∈ Submodule.span ℂ (Set.range (fun i : L => curve i)) := by
    have hc := congrArg contractRight h
    simp only [map_sum, map_smul, contractRight_tmul, witnessDual_value, one_smul] at hc
    rw [hc]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨t i, ht i⟩, rfl⟩
  have hvR : witnessVector ∈ Submodule.span ℂ (Set.range (fun i : R => curve i)) := by
    have hc := congrArg contractLeft h
    simp only [map_sum, map_smul, contractLeft_tmul, witnessDual_value, one_smul] at hc
    rw [hc]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨u i, hu i⟩, rfl⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hvL
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hvR
  choose f hf using fun i : L => curve_dual L hL i i.property
  choose g hg using fun j : R => curve_dual R hR j j.property
  have hfa (i : L) : f i witnessVector = a i := by
    rw [← ha, map_sum]
    have hfij (j : L) : f i (curve j) = if j = i then 1 else 0 := by
      simpa only [Subtype.ext_iff] using hf i j j.property
    simp [map_smul, hfij, smul_eq_mul, mul_ite]
  have hgb (j : R) : g j witnessVector = b j := by
    rw [← hb, map_sum]
    have hgij (i : R) : g j (curve i) = if i = j then 1 else 0 := by
      simpa only [Subtype.ext_iff] using hg j i i.property
    simp [map_smul, hgij, smul_eq_mul, mul_ite]
  let A : Finset L := Finset.univ.filter (fun i => a i ≠ 0)
  let B : Finset R := Finset.univ.filter (fun j => b j ≠ 0)
  have hA : 3 ≤ A.card := witness_expansion_support L a ha.symm
  have hB : 3 ≤ B.card := witness_expansion_support R b hb.symm
  let pairs : Finset (L × R) := Finset.univ.image (fun i => (⟨t i, ht i⟩, ⟨u i, hu i⟩))
  have hsub : A ×ˢ B ⊆ pairs := by
    rintro ⟨i, j⟩ hij
    have hai : a i ≠ 0 := (Finset.mem_filter.mp (Finset.mem_product.mp hij).1).2
    have hbj : b j ≠ 0 := (Finset.mem_filter.mp (Finset.mem_product.mp hij).2).2
    by_contra hnot
    have hzero : pairDual (f i) (g j) (witnessVector ⊗ₜ[ℂ] witnessVector) = 0 := by
      rw [h, map_sum]
      apply Finset.sum_eq_zero
      intro n _
      rw [map_smul, pairDual_tmul, hf i (t n) (ht n), hg j (u n) (hu n)]
      by_cases hti : t n = i
      · have hui : u n ≠ j := by
          intro huj
          apply hnot
          apply Finset.mem_image.mpr
          exact ⟨n, Finset.mem_univ _, Prod.ext (Subtype.ext hti) (Subtype.ext huj)⟩
        simp [hti, hui]
      · simp [hti]
    rw [pairDual_tmul, hfa, hgb] at hzero
    exact mul_ne_zero hai hbj hzero
  have hpairs : pairs.card ≤ k := (Finset.card_image_le).trans (by simp)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_product] at hcard
  have hnine : 9 ≤ A.card * B.card := by
    calc 9 = 3 * 3 := rfl
         _ ≤ A.card * B.card := Nat.mul_le_mul hA hB
  omega

theorem square_not_eight :
    ¬ TensorRankAtMost witnessVariety.cone 8 (witnessVector ⊗ₜ[ℂ] witnessVector) := by
  rintro ⟨k, hk, a, x, y, hxy, h⟩
  obtain ⟨d, t, u, hnorm⟩ := cone_square_parameters a x y (fun i => (hxy i).1)
    (fun i => (hxy i).2)
  exact square_parameter_lower_bound hk d t u (h.trans hnorm)

end NLA.TR27
