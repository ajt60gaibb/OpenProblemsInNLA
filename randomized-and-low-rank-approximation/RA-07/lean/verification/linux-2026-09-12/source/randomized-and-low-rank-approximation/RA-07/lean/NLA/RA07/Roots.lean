/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Root factorization for Matthew J. Colbrook's affirmative resolution of RA-07.
The proof reuses Mathlib's Gauss–Lucas theorem with full multiset multiplicities.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.RA07.Algebra
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Complex.Convex
import Mathlib.Data.List.OfFn

set_option autoImplicit false
open scoped BigOperators Polynomial Classical
noncomputable section

namespace NLA.RA07
open Polynomial

theorem generating_natDegree {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) : (generatingPolynomial lam).natDegree = n := by
  have hne (i : Fin n) : (1 + C (lam i) * X : ℝ[X]) ≠ 0 := by
    intro h
    have := congrArg (fun p : ℝ[X] => p.eval 0) h
    simp at this
  have hdeg (i : Fin n) : (1 + C (lam i) * X : ℝ[X]).natDegree = 1 := by
    rw [show (1 + C (lam i) * X : ℝ[X]) = C (lam i) * X + C 1 by simp [add_comm]]
    rw [natDegree_add_C, natDegree_C_mul (ne_of_gt (hlam i)), natDegree_X]
  rw [generatingPolynomial, natDegree_prod _ _ (fun i _ => hne i)]
  simp only [hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem iterated_derivative_natDegree (p : ℝ[X]) (d : ℕ) :
    ((derivative^[d]) p).natDegree = p.natDegree - d := by
  induction d with
  | zero => simp
  | succ d ih => simp only [Function.iterate_succ_apply', natDegree_derivative, ih, Nat.sub_sub]

theorem generating_derivative_natDegree {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (d : ℕ) :
    (iteratedGeneratingDerivative lam d).natDegree = n - d := by
  rw [iteratedGeneratingDerivative, iterated_derivative_natDegree, generating_natDegree lam hlam]

theorem generating_derivative_eval_pos {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (d : ℕ) (hd : d ≤ n) :
    0 < (iteratedGeneratingDerivative lam d).eval 0 := by
  rw [(generating_derivative_values_proved lam d).2]
  exact mul_pos (by exact_mod_cast Nat.factorial_pos d)
    ((elementary_values_proved lam hlam).2.2 d hd)

/-- This open real ray is convex inside the actual complex plane. -/
theorem convex_negative_real_ray :
    Convex ℝ {z : ℂ | z.im = 0 ∧ z.re < 0} := by
  intro x hx y hy a b ha hb hab
  constructor
  · simp [hx.1, hy.1]
  · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    rcases eq_or_lt_of_le ha with hzero | hpos
    · have hb1 : b = 1 := by linarith
      simpa [← hzero, hb1] using hy.2
    · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg hpos hx.2)
        (mul_nonpos_of_nonneg_of_nonpos hb hy.2.le)

theorem generating_complex_roots_negative {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) :
    ((generatingPolynomial lam).map Complex.ofRealHom).rootSet ℂ ⊆
      {z : ℂ | z.im = 0 ∧ z.re < 0} := by
  intro z hz
  have he := (mem_rootSet.mp hz).2
  simp only [coe_aeval_eq_eval, generatingPolynomial, Polynomial.map_prod, Polynomial.map_add,
    Polynomial.map_one, Polynomial.map_mul, map_C, map_X, eval_prod,
    eval_add, eval_one, eval_mul, eval_C, eval_X] at he
  change (∏ i : Fin n, (1 + (lam i : ℂ) * z)) = 0 at he
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp he
  have hre := congrArg Complex.re hi
  have him := congrArg Complex.im hi
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at hre
  simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, zero_add, Complex.zero_im] at him
  refine ⟨(mul_eq_zero.mp him).resolve_left (ne_of_gt (hlam i)), ?_⟩
  nlinarith [hlam i]

theorem derivative_complex_roots_negative {p : ℂ[X]} (hp : 0 < p.degree)
    (hroots : p.rootSet ℂ ⊆ {z : ℂ | z.im = 0 ∧ z.re < 0}) :
    p.derivative.rootSet ℂ ⊆ {z : ℂ | z.im = 0 ∧ z.re < 0} :=
  (rootSet_derivative_subset_convexHull_rootSet hp).trans
    (convexHull_min hroots convex_negative_real_ray)

theorem iterated_complex_roots_negative {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (d : ℕ) (hd : d ≤ n) :
    ((iteratedGeneratingDerivative lam d).map Complex.ofRealHom).rootSet ℂ ⊆
      {z : ℂ | z.im = 0 ∧ z.re < 0} := by
  induction d with
  | zero => simpa [iteratedGeneratingDerivative] using generating_complex_roots_negative lam hlam
  | succ d ih =>
    have hdn : d < n := by omega
    have hp : 0 < ((iteratedGeneratingDerivative lam d).map Complex.ofRealHom).degree := by
      rw [← natDegree_pos_iff_degree_pos, natDegree_map]
      rw [generating_derivative_natDegree lam hlam]
      omega
    have hr := derivative_complex_roots_negative hp (ih (by omega))
    simpa only [iteratedGeneratingDerivative, Function.iterate_succ_apply', derivative_map] using hr

theorem complex_rootSet_of_mem_roots {p : ℂ[X]} {z : ℂ} (hz : z ∈ p.roots) :
    z ∈ p.rootSet ℂ := by
  apply mem_rootSet.mpr
  exact ⟨ne_zero_of_mem_roots hz, by
    simpa only [coe_aeval_eq_eval, IsRoot.def] using (isRoot_of_mem_roots hz)⟩

/-- Descending from complex roots retains the complete real multiset of roots. -/
theorem real_splits_of_negative_complex_roots (p : ℝ[X])
    (hroots : (p.map Complex.ofRealHom).rootSet ℂ ⊆
      {z : ℂ | z.im = 0 ∧ z.re < 0}) : p.Splits := by
  apply Splits.of_splits_map Complex.ofRealHom (IsAlgClosed.splits _)
  intro z hz
  have him := (hroots (complex_rootSet_of_mem_roots hz)).1
  refine ⟨z.re, ?_⟩
  apply Complex.ext
  · rfl
  · change (z.re : ℂ).im = z.im
    simpa only [Complex.ofReal_im] using him.symm

theorem real_factorization_of_negative_complex_roots (p : ℝ[X])
    (hroots : (p.map Complex.ofRealHom).rootSet ℂ ⊆
      {z : ℂ | z.im = 0 ∧ z.re < 0}) :
    ∃ μ : Fin p.natDegree → ℝ, (∀ a, 0 < μ a) ∧
      p = C (p.eval 0) * generatingPolynomial μ := by
  have hs := real_splits_of_negative_complex_roots p hroots
  have hn (r : ℝ) (hr : r ∈ p.roots) : r < 0 := by
    have hm : (r : ℂ) ∈ (p.map Complex.ofRealHom).roots := by
      rw [hs.roots_map]
      exact Multiset.mem_map.mpr ⟨r, hr, rfl⟩
    exact (hroots (complex_rootSet_of_mem_roots hm)).2
  rw [hs.natDegree_eq_card_roots, ← Multiset.length_toList]
  let L := p.roots.toList
  let r : Fin L.length → ℝ := L.get
  have hr (a : Fin L.length) : r a ∈ p.roots := by
    exact Multiset.mem_toList.mp (List.get_mem L a)
  let μ : Fin L.length → ℝ := fun a => -(r a)⁻¹
  refine ⟨μ, fun a => neg_pos.mpr (inv_neg''.mpr (hn (r a) (hr a))), ?_⟩
  have hprod (g : ℝ → ℝ[X]) : (p.roots.map g).prod = ∏ a : Fin L.length, g (r a) := by
    rw [← Fin.prod_ofFn]
    have he : List.ofFn (fun a : Fin L.length => g (r a)) = L.map g := by
      rw [show (fun a : Fin L.length => g (r a)) = g ∘ L.get by rfl,
        ← List.map_ofFn, List.ofFn_get]
    rw [he]
    simp [L]
  have hlin (a : Fin L.length) : X - C (r a) =
      C (-r a) * (1 + C (μ a) * X) := by
    have hne : r a ≠ 0 := ne_of_lt (hn (r a) (hr a))
    dsimp [μ]
    rw [mul_add, mul_one, ← mul_assoc, ← C_mul]
    simp only [neg_mul_neg, mul_inv_cancel₀ hne, C_1, one_mul, C_neg]
    ring
  have hfac : p = C (p.leadingCoeff * ∏ a : Fin L.length, -r a) * generatingPolynomial μ := by
    calc
      p = C p.leadingCoeff * (p.roots.map (fun a => X - C a)).prod := hs.eq_prod_roots
      _ = C p.leadingCoeff * ∏ a : Fin L.length, (X - C (r a)) := by rw [hprod]
      _ = C (p.leadingCoeff * ∏ a : Fin L.length, -r a) * generatingPolynomial μ := by
        simp_rw [hlin]
        rw [Finset.prod_mul_distrib]
        simp [generatingPolynomial, mul_assoc]
  have heval : p.eval 0 = p.leadingCoeff * ∏ a : Fin L.length, -r a := by
    have he := congrArg (fun q : ℝ[X] => q.eval 0) hfac
    simpa only [eval_mul, eval_C, generatingPolynomial, eval_prod,
      eval_add, eval_one, eval_mul, eval_C, eval_X, mul_zero, add_zero,
      Finset.prod_const_one, mul_one] using he
  rw [heval]
  exact hfac

theorem positive_derivative_factorization_proved {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (d : ℕ) (hd : d ≤ n) :
    0 < (iteratedGeneratingDerivative lam d).eval 0 ∧
    (iteratedGeneratingDerivative lam d).natDegree = n - d ∧
    ∃ μ : Fin (n - d) → ℝ, (∀ a, 0 < μ a) ∧
      iteratedGeneratingDerivative lam d =
        C ((iteratedGeneratingDerivative lam d).eval 0) * generatingPolynomial μ := by
  refine ⟨generating_derivative_eval_pos lam hlam d hd,
    generating_derivative_natDegree lam hlam d, ?_⟩
  have h := real_factorization_of_negative_complex_roots (iteratedGeneratingDerivative lam d)
    (iterated_complex_roots_negative lam hlam d hd)
  exact (generating_derivative_natDegree lam hlam d) ▸ h

end NLA.RA07
