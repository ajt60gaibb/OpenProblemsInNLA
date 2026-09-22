/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical counterexample: Matthew J. Colbrook.
AI-assisted polynomial-dual proof following the reviewed statement freeze.
-/
import NLA.TR27.Algebra
import NLA.TR27.IntegralImage
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct LinearAlgebra.Projectivization
open Polynomial
namespace NLA.TR27

/-- Pair a polynomial's first thirteen coefficients with a source vector. -/
def coefficientFunctional (f : ℂ[X]) : SourceSpace →ₗ[ℂ] ℂ :=
  ∑ j : Fin 13, f.coeff (j : ℕ) • LinearMap.proj j

theorem coefficientFunctional_apply (f : ℂ[X]) (v : SourceSpace) :
    coefficientFunctional f v = ∑ j : Fin 13, f.coeff (j : ℕ) * v j := by
  simp [coefficientFunctional]

theorem coefficientFunctional_sourceUnit (f : ℂ[X]) (i : Fin 13) :
    coefficientFunctional f (sourceUnit i) = f.coeff (i : ℕ) := by
  classical
  simp [coefficientFunctional_apply, sourceUnit, mul_ite]

theorem coefficientFunctional_some (f : ℂ[X]) (hf : f.natDegree ≤ 12) (a : ℂ) :
    coefficientFunctional f (sourceCurve (some a)) = f.eval a := by
  rw [coefficientFunctional_apply, Polynomial.eval_eq_sum,
    Polynomial.sum_over_range' f (fun n => zero_mul (a ^ n)) 13 (by omega)]
  simpa [sourceCurve] using
    (Fin.sum_univ_eq_sum_range (fun j => f.coeff j * a ^ j) 13)

theorem coefficientFunctional_none (f : ℂ[X]) :
    coefficientFunctional f (sourceCurve none) = f.coeff 12 := by
  exact coefficientFunctional_sourceUnit f 12

/-- Factors omit infinity and zero; the initial X handles finite zero. -/
def tangentFactor : Option ℂ → ℂ[X]
  | none => 1
  | some a => if a = 0 then 1 else X - C a

def tangentPolynomial {k : ℕ} (t : Fin k → Option ℂ) : ℂ[X] :=
  X * ∏ i, tangentFactor (t i)

theorem tangentFactor_degree (t : Option ℂ) : (tangentFactor t).natDegree ≤ 1 := by
  cases t with
  | none => simp [tangentFactor]
  | some a => by_cases ha : a = 0 <;> simp [tangentFactor, ha]

theorem tangentFactor_coeff_zero (t : Option ℂ) : (tangentFactor t).coeff 0 ≠ 0 := by
  cases t with
  | none => simp [tangentFactor]
  | some a => by_cases ha : a = 0 <;> simp [tangentFactor, ha]

theorem tangentPolynomial_degree {k : ℕ} (t : Fin k → Option ℂ) :
    (tangentPolynomial t).natDegree ≤ k + 1 := by
  have hp : (∏ i, tangentFactor (t i)).natDegree ≤ k := by
    calc
      _ ≤ ∑ i, (tangentFactor (t i)).natDegree := Polynomial.natDegree_prod_le Finset.univ _
      _ ≤ ∑ _i : Fin k, 1 := Finset.sum_le_sum (fun i _ => tangentFactor_degree (t i))
      _ = k := by simp
  have := Polynomial.natDegree_mul_le (p := (X : ℂ[X]))
    (q := ∏ i, tangentFactor (t i))
  simp only [Polynomial.natDegree_X] at this
  dsimp [tangentPolynomial]
  omega

theorem tangentPolynomial_degree_of_none {k : ℕ} (t : Fin k → Option ℂ)
    (i : Fin k) (hi : t i = none) : (tangentPolynomial t).natDegree ≤ k := by
  have hs : (∑ j, (tangentFactor (t j)).natDegree) < k := by
    have hlt := Finset.sum_lt_sum
      (s := Finset.univ) (f := fun j => (tangentFactor (t j)).natDegree)
      (g := fun _j : Fin k => 1)
      (fun j _ => tangentFactor_degree (t j))
      ⟨i, Finset.mem_univ i, by simp [hi, tangentFactor]⟩
    simpa using hlt
  have hp : (∏ j, tangentFactor (t j)).natDegree < k :=
    lt_of_le_of_lt (Polynomial.natDegree_prod_le Finset.univ _) hs
  have hmul := Polynomial.natDegree_mul_le (p := (X : ℂ[X]))
    (q := ∏ j, tangentFactor (t j))
  simp only [Polynomial.natDegree_X] at hmul
  dsimp [tangentPolynomial]
  omega

theorem tangentPolynomial_coeff_one {k : ℕ} (t : Fin k → Option ℂ) :
    (tangentPolynomial t).coeff 1 ≠ 0 := by
  rw [tangentPolynomial, show 1 = 0 + 1 from rfl, Polynomial.coeff_X_mul,
    Polynomial.coeff_zero_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => tangentFactor_coeff_zero (t i))

theorem tangentPolynomial_eval {k : ℕ} (t : Fin k → Option ℂ)
    (i : Fin k) (a : ℂ) (hi : t i = some a) : (tangentPolynomial t).eval a = 0 := by
  by_cases ha : a = 0
  · simp [tangentPolynomial, ha]
  · simp only [tangentPolynomial, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_prod]
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi, tangentFactor, ha]

theorem tangentPolynomial_annihilates {k : ℕ} (hk : k ≤ 11)
    (t : Fin k → Option ℂ) (i : Fin k) :
    coefficientFunctional (tangentPolynomial t) (sourceCurve (t i)) = 0 := by
  cases hti : t i with
  | none =>
      rw [coefficientFunctional_none]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (tangentPolynomial_degree_of_none t i hti) (by omega))
  | some a =>
      rw [coefficientFunctional_some _ (by have := tangentPolynomial_degree t; omega)]
      exact tangentPolynomial_eval t i a hti

/-- The tangent vector cannot be expressed with eleven or fewer curve vectors.
Repetitions, finite zero, and infinity are all allowed in the putative sum. -/
theorem tangent_not_sum {k : ℕ} (hk : k ≤ 11) (t : Fin k → Option ℂ)
    (a : Fin k → ℂ) : sourceUnit 1 ≠ ∑ i, a i • sourceCurve (t i) := by
  intro h
  have hp := congrArg (coefficientFunctional (tangentPolynomial t)) h
  simp only [coefficientFunctional_sourceUnit, map_sum, map_smul,
    tangentPolynomial_annihilates hk, smul_zero, Finset.sum_const_zero] at hp
  exact tangentPolynomial_coeff_one t hp

/-- A product factor omits the distinguished index and infinity. -/
def separatingFactor {k : ℕ} (t : Fin k → Option ℂ) (i j : Fin k) : ℂ[X] :=
  if j = i then 1 else
    match t j with
    | none => 1
    | some a => X - C a

def separatingPolynomial {k : ℕ} (t : Fin k → Option ℂ) (i : Fin k) : ℂ[X] :=
  ∏ j, separatingFactor t i j

theorem separatingFactor_degree {k : ℕ} (t : Fin k → Option ℂ) (i j : Fin k) :
    (separatingFactor t i j).natDegree ≤ 1 := by
  by_cases hij : j = i
  · simp [separatingFactor, hij]
  · cases h : t j <;> simp [separatingFactor, hij, h]

theorem separatingPolynomial_degree {k : ℕ} (t : Fin k → Option ℂ) (i : Fin k) :
    (separatingPolynomial t i).natDegree ≤ k := by
  calc
    _ ≤ ∑ j, (separatingFactor t i j).natDegree :=
      Polynomial.natDegree_prod_le Finset.univ _
    _ ≤ ∑ _j : Fin k, 1 := Finset.sum_le_sum (fun j _ => separatingFactor_degree t i j)
    _ = k := by simp

theorem separatingPolynomial_eval_self {k : ℕ} (t : Fin k → Option ℂ)
    (ht : Function.Injective t) (i : Fin k) (a : ℂ) (hi : t i = some a) :
    (separatingPolynomial t i).eval a ≠ 0 := by
  classical
  rw [separatingPolynomial, Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  by_cases hji : j = i
  · simp [separatingFactor, hji]
  · cases hj : t j with
    | none => simp [separatingFactor, hji, hj]
    | some b =>
        have hab : a ≠ b := by
          intro hab
          exact hji (ht (hi.trans ((congrArg some hab).trans hj.symm))).symm
        simpa [separatingFactor, hji, hj] using sub_ne_zero.mpr hab

theorem separatingPolynomial_eval_other {k : ℕ} (t : Fin k → Option ℂ)
    (i j : Fin k) (hji : j ≠ i) (a : ℂ) (hj : t j = some a) :
    (separatingPolynomial t i).eval a = 0 := by
  rw [separatingPolynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [separatingFactor, hji, hj]

theorem separatingPolynomial_annihilates {k : ℕ} (hk : k ≤ 8)
    (t : Fin k → Option ℂ) (i j : Fin k) (hji : j ≠ i) :
    coefficientFunctional (separatingPolynomial t i) (sourceCurve (t j)) = 0 := by
  cases hj : t j with
  | none =>
      rw [coefficientFunctional_none]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (separatingPolynomial_degree t i) (by omega))
  | some a =>
      rw [coefficientFunctional_some _ (by have := separatingPolynomial_degree t i; omega)]
      exact separatingPolynomial_eval_other t i j hji a hj

/-- Eight distinct source points are independent, including the infinity point. -/
theorem source_curve_independent {k : ℕ} (hk : k ≤ 8) (t : Fin k → Option ℂ)
    (ht : Function.Injective t) : LinearIndependent ℂ (fun i => sourceCurve (t i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have hfinite : ∀ i b, t i = some b → a i = 0 := by
    intro i b hib
    have hpair := congrArg (coefficientFunctional (separatingPolynomial t i)) ha
    simp only [map_sum, map_smul, map_zero] at hpair
    have hsum :
        (∑ j, a j • coefficientFunctional (separatingPolynomial t i) (sourceCurve (t j))) =
        a i • coefficientFunctional (separatingPolynomial t i) (sourceCurve (t i)) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [separatingPolynomial_annihilates hk t i j hji, smul_zero]
      · simp
    rw [hsum, hib, coefficientFunctional_some _
      (by have := separatingPolynomial_degree t i; omega)] at hpair
    exact (mul_eq_zero.mp hpair).resolve_right (separatingPolynomial_eval_self t ht i b hib)
  intro i
  cases hi : t i with
  | some b => exact hfinite i b hi
  | none =>
      have hsum : (∑ j, a j • sourceCurve (t j)) = a i • sourceCurve (t i) := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          cases hj : t j with
          | none => exact (hji (ht (hj.trans hi.symm))).elim
          | some b => rw [hfinite j b hj, zero_smul]
        · simp
      have hzero : a i • sourceUnit 12 = 0 := by simpa [hi, sourceCurve] using hsum.symm.trans ha
      have hlast := congrFun hzero 12
      simpa [sourceUnit] using hlast

theorem tangent_not_span {k : ℕ} (hk : k ≤ 11) (t : Fin k → Option ℂ) :
    sourceUnit 1 ∉ Submodule.span ℂ (Set.range (fun i => sourceCurve (t i))) := by
  intro h
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp h
  exact tangent_not_sum hk t a ha.symm

/-- Adding the three fixed source points to any eight proposed center terms
would give a forbidden expression of the tangent vector using eleven terms. -/
theorem center_not_span {k : ℕ} (hk : k ≤ 8) (t : Fin k → Option ℂ) :
    center ∉ Submodule.span ℂ (Set.range (fun i => sourceCurve (t i))) := by
  classical
  intro hcenter
  let u : Fin (k + 3) → Option ℂ := Fin.append t ![some 1, some 2, some 3]
  let S := Submodule.span ℂ (Set.range (fun i => sourceCurve (u i)))
  have ht : Submodule.span ℂ (Set.range (fun i => sourceCurve (t i))) ≤ S := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    apply Submodule.subset_span
    exact ⟨Fin.castAdd 3 i, by simp [u]⟩
  have hfixed (i : Fin 3) : sourceCurve (![some 1, some 2, some 3] i) ∈ S := by
    apply Submodule.subset_span
    exact ⟨Fin.natAdd k i, by simp [u]⟩
  have h1 : sourceCurve (some 1) ∈ S := by simpa using hfixed 0
  have h2 : sourceCurve (some 2) ∈ S := by simpa using hfixed 1
  have h3 : sourceCurve (some 3) ∈ S := by simpa using hfixed 2
  have he : sourceUnit 1 = center + sourceCurve (some 1) + sourceCurve (some 2) +
      sourceCurve (some 3) := by
    rw [center]
    abel
  apply tangent_not_span (by omega : k + 3 ≤ 11) u
  rw [he]
  exact S.add_mem (S.add_mem (S.add_mem (ht hcenter) h1) h2) h3

/-- The projection preserves independence uniformly on every set of at most
eight distinct parameters, with no restriction to generic or finite points. -/
theorem projected_curve_independent {k : ℕ} (hk : k ≤ 8) (t : Fin k → Option ℂ)
    (ht : Function.Injective t) : LinearIndependent ℂ (fun i => curve (t i)) := by
  have hker : LinearMap.ker quotientLinearMap = Submodule.span ℂ {center} :=
    SetLike.coe_injective quotientMap_kernel
  have hdisjoint : Disjoint (Submodule.span ℂ (Set.range (fun i => sourceCurve (t i))))
      (LinearMap.ker quotientLinearMap) := by
    rw [hker]
    exact Submodule.disjoint_span_singleton_of_notMem (center_not_span hk t)
  have hli := (quotientLinearMap.linearIndependent_iff_of_disjoint hdisjoint).mpr
    (source_curve_independent hk t ht)
  simpa only [Function.comp_def, quotientLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    curve] using hli

/-- Whole-image equality supplies an actual finite or infinity parameter for
every point of the algebraic variety, not merely a dense subset. -/
theorem projective_curve_representation (p : ℙ ℂ Space) (hp : p ∈ witnessVariety.points) :
    ∃ t : Option ℂ, p = Projectivization.mk ℂ (curve t) (curve_nonzero t) := by
  have hc : p.rep ∈ parameterizedCone := by
    rw [← whole_closed_image.2]
    exact hp
  rcases hc with hz | ⟨a, _ha, t, ht⟩
  · exact (p.rep_nonzero hz).elim
  · refine ⟨t, ?_⟩
    calc
      p = Projectivization.mk ℂ p.rep p.rep_nonzero := (Projectivization.mk_rep p).symm
      _ = Projectivization.mk ℂ (curve t) (curve_nonzero t) :=
        (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨a, ht.symm⟩

/-- The complete frozen uniform-independence statement on the whole variety. -/
theorem eight_point_independence (k : ℕ) (hk : k ≤ 8)
    (p : Fin k → ℙ ℂ Space) (hp : ∀ i, p i ∈ witnessVariety.points)
    (hi : Function.Injective p) : Projectivization.Independent p := by
  classical
  choose t ht using fun i => projective_curve_representation (p i) (hp i)
  have hinj : Function.Injective t := by
    intro i j hij
    apply hi
    rw [ht i, ht j, hij]
  have heq : p = fun i => Projectivization.mk ℂ (curve (t i)) (curve_nonzero (t i)) :=
    funext ht
  rw [heq]
  exact Projectivization.Independent.mk _ (fun i => curve_nonzero (t i))
    (projected_curve_independent hk t hinj)

end NLA.TR27
