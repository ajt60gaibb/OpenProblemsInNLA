/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted formalization by agent /root/recover_published_coverage.

Finite incidence-count implementation of the contact-count step in Matthew
J. Colbrook's NR-04 proof, University of Cambridge. This module does not
assert that an arbitrary affine section has a finite extreme-point hull;
that geometric prerequisite must still be proved before applying this to C09.
Weighted double counting reuses Mathlib's existing Finset bipartite API.
-/
import NLA.NR04.SectionLinearAlgebra
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace NLA.NR04

/-- A finite incidence relation with right degree at most two, positive left
degrees, and isolated right neighbors for degree-one left vertices has at
least as many right vertices as left vertices. -/
lemma incidence_card_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : ι → κ → Prop) [DecidableRel R]
    (hleft : ∀ i, 0 < (Finset.univ.bipartiteAbove R i).card)
    (hright : ∀ k, (Finset.univ.bipartiteBelow R k).card ≤ 2)
    (hsingle : ∀ i k, R i k →
      (Finset.univ.bipartiteAbove R i).card = 1 →
      (Finset.univ.bipartiteBelow R k).card ≤ 1) :
    Fintype.card ι ≤ Fintype.card κ := by
  classical
  let L (i : ι) : Finset κ := Finset.univ.bipartiteAbove R i
  let B (k : κ) : Finset ι := Finset.univ.bipartiteBelow R k
  let d (i : ι) : ℕ := (L i).card
  let w (i : ι) : ℝ := 1 / (d i : ℝ)
  have hdpos (i : ι) : 0 < (d i : ℝ) := by
    have h : 0 < d i := hleft i
    exact_mod_cast h
  have hwone (i : ι) : w i ≤ 1 := by
    have h : (1 : ℝ) ≤ (d i : ℝ) := by
      have h' : 1 ≤ d i := hleft i
      exact_mod_cast h'
    exact (div_le_iff₀ (hdpos i)).mpr (by simpa using h)
  have hwhalf (i : ι) (hi : 2 ≤ d i) : w i ≤ 1 / 2 := by
    have h : (2 : ℝ) ≤ (d i : ℝ) := by exact_mod_cast hi
    apply (div_le_iff₀ (hdpos i)).mpr
    linarith
  have hrow (i : ι) : (∑ k ∈ L i, w i) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    change (d i : ℝ) * (1 / (d i : ℝ)) = 1
    exact mul_one_div_cancel (ne_of_gt (hdpos i))
  have hcol (k : κ) : (∑ i ∈ B k, w i) ≤ 1 := by
    have hk : (B k).card ≤ 2 := hright k
    have hcases : (B k).card = 0 ∨ (B k).card = 1 ∨ (B k).card = 2 := by
      omega
    rcases hcases with h0 | h1 | h2
    · have hb : B k = ∅ := Finset.card_eq_zero.mp h0
      simp [hb]
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
      simpa [hi] using hwone i
    · obtain ⟨i, j, hij, hB⟩ := Finset.card_eq_two.mp h2
      have hRi : R i k := by
        have hi : i ∈ B k := by simp [hB]
        simpa [B] using hi
      have hRj : R j k := by
        have hj : j ∈ B k := by simp [hB]
        simpa [B] using hj
      have htwo (a : ι) (ha : R a k) : 2 ≤ d a := by
        by_contra h
        have hd : d a = 1 := by
          have hp : 0 < d a := hleft a
          omega
        have hb : (B k).card ≤ 1 := hsingle a k ha hd
        omega
      calc
        (∑ a ∈ B k, w a) = w i + w j := by simp [hB, hij]
        _ ≤ 1 / 2 + 1 / 2 := add_le_add (hwhalf i (htwo i hRi))
          (hwhalf j (htwo j hRj))
        _ = 1 := by norm_num
  have hcard : (Fintype.card ι : ℝ) ≤ (Fintype.card κ : ℝ) := by
    calc
      (Fintype.card ι : ℝ) = ∑ i : ι, ∑ k ∈ L i, w i := by simp [hrow]
      _ = ∑ k : κ, ∑ i ∈ B k, w i := by
        simpa only [L, B] using
          (Finset.sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow
            (s := Finset.univ) (t := Finset.univ) R (fun i _ => w i))
      _ ≤ ∑ _k : κ, (1 : ℝ) := Finset.sum_le_sum (fun k _ => hcol k)
      _ = (Fintype.card κ : ℝ) := by simp
  exact_mod_cast hcard

/-- The positive off-diagonal factor pattern supplies the incidence hypotheses.
Only literal nonnegative factors and a proved two-zero bound are inputs. -/
lemma factor_width_ge_order_of_two_zeros {N m : ℕ}
    (X : Matrix (Fin N) (Fin N) ℝ)
    (V : Matrix (Fin N) (Fin m) ℝ) (A : Matrix (Fin m) (Fin N) ℝ)
    (hN : 2 ≤ N) (hV : EntrywiseNonnegative V) (hA : EntrywiseNonnegative A)
    (hVA : V * A = X) (hdiag : ∀ i, X i i = 0)
    (hoff : ∀ i j, i ≠ j → 0 < X i j)
    (hzeros : ∀ r, (Finset.univ.filter fun i => V i r = 0).card ≤ 2) :
    N ≤ m := by
  classical
  letI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr hN
  let R (i : Fin N) (r : Fin m) : Prop := V i r = 0
  have hdiagTerm (i : Fin N) (r : Fin m) : V i r * A r i = 0 := by
    have hsum : (∑ s, V i s * A s i) = 0 := by
      change (V * A) i i = 0
      rw [hVA, hdiag]
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun s _ => mul_nonneg (hV i s) (hA s i))).mp hsum r (Finset.mem_univ r)
  have hleft (j : Fin N) : 0 < (Finset.univ.bipartiteAbove R j).card := by
    obtain ⟨i, hij⟩ := exists_ne j
    have hsum : 0 < ∑ r, V i r * A r j := by
      change 0 < (V * A) i j
      rw [hVA]
      exact hoff i j hij
    obtain ⟨r, _, hr⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun s _ => mul_nonneg (hV i s) (hA s j))).mp hsum
    have hAr : A r j ≠ 0 := by
      intro h
      simp [h] at hr
    have hVjr : V j r = 0 := (mul_eq_zero.mp (hdiagTerm j r)).resolve_right hAr
    apply Finset.card_pos.mpr
    exact ⟨r, by simp [R, hVjr]⟩
  have hright (r : Fin m) : (Finset.univ.bipartiteBelow R r).card ≤ 2 := by
    simpa only [Finset.bipartiteBelow, R] using hzeros r
  have hsingle (i : Fin N) (r : Fin m) (hir : R i r)
      (hi : (Finset.univ.bipartiteAbove R i).card = 1) :
      (Finset.univ.bipartiteBelow R r).card ≤ 1 := by
    obtain ⟨r₀, hr₀⟩ := Finset.card_eq_one.mp hi
    have hrr₀ : r = r₀ := by
      have hr : r ∈ Finset.univ.bipartiteAbove R i := by simp [hir]
      rw [hr₀] at hr
      exact Finset.mem_singleton.mp hr
    subst r₀
    have hsub : Finset.univ.bipartiteBelow R r ⊆ {i} := by
      intro j hj
      have hVjr : V j r = 0 := by simpa [R] using hj
      have hji : j = i := by
        by_contra hji
        have hzero : X j i = 0 := by
          rw [← hVA, Matrix.mul_apply]
          apply Finset.sum_eq_zero
          intro s _
          by_cases his : V i s = 0
          · have hs : s = r := by
              have hmem : s ∈ Finset.univ.bipartiteAbove R i := by simp [R, his]
              rw [hr₀] at hmem
              exact Finset.mem_singleton.mp hmem
            simp [hs, hVjr]
          · have hAs : A s i = 0 := (mul_eq_zero.mp (hdiagTerm i s)).resolve_left his
            simp [hAs]
        exact (ne_of_gt (hoff j i hji)) hzero
      exact Finset.mem_singleton.mpr hji
    simpa using Finset.card_le_card hsub
  simpa only [Fintype.card_fin] using incidence_card_le R hleft hright hsingle

/-- Every exact nonnegative factorization whose left columns lie in the
normalized rank-three affine plane uses at least N columns. To apply this
to C09, the actual finite extreme-point hull still has to be established. -/
lemma factor_width_ge_order_of_column_plane {N m : ℕ}
    (X : Matrix (Fin N) (Fin N) ℝ)
    (V : Matrix (Fin N) (Fin m) ℝ) (A : Matrix (Fin m) (Fin N) ℝ)
    (hX : ColumnStochastic X) (hrX : X.rank = 3)
    (hdiag : ∀ i, X i i = 0) (hoff : ∀ i j, i ≠ j → 0 < X i j)
    (hV : EntrywiseNonnegative V) (hA : EntrywiseNonnegative A) (hVA : V * A = X)
    (hplane : ∀ r, (fun i => V i r) ∈ columnAffineSpan X) : N ≤ m := by
  have hN : 2 ≤ N := by
    have h := Matrix.rank_le_width X
    rw [hrX] at h
    omega
  apply factor_width_ge_order_of_two_zeros X V A hN hV hA hVA hdiag hoff
  intro r
  exact zero_coordinate_card_le_two X hX hrX hdiag hoff (fun i => V i r) (hplane r)

#print axioms incidence_card_le
#print axioms factor_width_ge_order_of_two_zeros
#print axioms factor_width_ge_order_of_column_plane

end NLA.NR04
