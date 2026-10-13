import NLA.TR13.Upper
import NLA.TR13.Lower
import NLA.TR13.RankComparison
import NLA.TR13.WidthDefinitions
import LeanCert.Tactic.Verification

/-!
The existing TR-13 solution gives equality of the five minimum ranks.  The
frozen shared statement asks for equivalence of the five width-at-most
predicates at every width.  This module derives that stronger, exact
statement shape directly from the existing generic upper and lower bounds.
-/

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators

namespace NLA.TR13

private theorem sum_fin_extend {α : Type*} [AddCommMonoid α]
    {q r : ℕ} (hqr : q ≤ r) (f : Fin q → α) :
    (∑ j : Fin r, if hj : j.val < q then f ⟨j.val, hj⟩ else 0) =
      ∑ j : Fin q, f j := by
  classical
  let g : ℕ → α := fun i => if hi : i < q then f ⟨i, hi⟩ else 0
  have hhead : (∑ i ∈ Finset.range q, g i) = ∑ j : Fin q, f j := by
    rw [Finset.sum_fin_eq_sum_range]
  have htail : (∑ i ∈ Finset.range (r - q), g (q + i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [g, Nat.not_lt.mpr (Nat.le_add_right q i)]
  calc
    (∑ j : Fin r, if hj : j.val < q then f ⟨j.val, hj⟩ else 0) =
        ∑ i ∈ Finset.range r, g i := by
      simpa only [g] using (Fin.sum_univ_eq_sum_range g r)
    _ = ∑ i ∈ Finset.range (q + (r - q)), g i := by
      rw [Nat.add_sub_of_le hqr]
    _ = (∑ i ∈ Finset.range q, g i) +
          ∑ i ∈ Finset.range (r - q), g (q + i) := Finset.sum_range_add g q (r - q)
    _ = ∑ j : Fin q, f j := by rw [hhead, htail, add_zero]

/-- Pad an actual homogeneous Vandermonde decomposition with zero coefficients.
The added projective pairs are `(1,0)`, so the nonzero-pair requirement is
preserved even at width zero. -/
theorem vandermondeRankAtMost_mono {m n q r : ℕ} {T : Tensor m n}
    (hqr : q ≤ r) (h : VandermondeRankAtMost q T) :
    VandermondeRankAtMost r T := by
  obtain ⟨c, a, b, hnz, hT⟩ := h
  let c' : Fin r → ℂ := fun j => if hj : j.val < q then c ⟨j.val, hj⟩ else 0
  let a' : Fin r → ℂ := fun j => if hj : j.val < q then a ⟨j.val, hj⟩ else 1
  let b' : Fin r → ℂ := fun j => if hj : j.val < q then b ⟨j.val, hj⟩ else 0
  refine ⟨c', a', b', ?_, ?_⟩
  · intro j
    by_cases hj : j.val < q
    · simpa [a', b', hj] using hnz ⟨j.val, hj⟩
    · simp [a', b', hj]
  · have hterm (j : Fin r) :
        c' j • symmetricTensor (m := m) (vandermondeVector n (a' j) (b' j)) =
          if hj : j.val < q then
            c ⟨j.val, hj⟩ •
              symmetricTensor (m := m)
                (vandermondeVector n (a ⟨j.val, hj⟩) (b ⟨j.val, hj⟩))
          else 0 := by
      by_cases hj : j.val < q <;> simp [c', a', b', hj]
    calc
      T = ∑ j : Fin q,
          c j • symmetricTensor (vandermondeVector n (a j) (b j)) := hT
      _ = ∑ j : Fin r, if hj : j.val < q then
            c ⟨j.val, hj⟩ •
              symmetricTensor (vandermondeVector n (a ⟨j.val, hj⟩) (b ⟨j.val, hj⟩))
          else 0 := (sum_fin_extend hqr _).symm
      _ = ∑ j : Fin r,
          c' j • symmetricTensor (vandermondeVector n (a' j) (b' j)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact (hterm j).symm

/-- An actual Vandermonde upper witness and a lower bound for every ambient
ordinary-border witness imply all four width equivalences at every width. -/
theorem equalFiveWidths_of_bounds {m n r : ℕ} (hm : 0 < m)
    {T : Tensor m n} (hu : VandermondeRankAtMost r T)
    (hl : ∀ q, OrdinaryBorderRankAtMost q T → r ≤ q) :
    EqualFiveWidths T := by
  intro q
  have hordinary_to_vandermonde (ho : OrdinaryRankAtMost q T) :
      VandermondeRankAtMost q T :=
    vandermondeRankAtMost_mono (hl q (ordinary_le_border ho)) hu
  have hvandermonde_to_ordinary (hv : VandermondeRankAtMost q T) :
      OrdinaryRankAtMost q T :=
    symmetric_le_ordinary hm (vandermonde_le_symmetric hv)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨fun ho => vandermonde_le_symmetric (hordinary_to_vandermonde ho),
      symmetric_le_ordinary hm⟩
  · exact ⟨ordinary_le_border, fun hb =>
      hvandermonde_to_ordinary (vandermondeRankAtMost_mono (hl q hb) hu)⟩
  · exact ⟨fun ho => symmetric_le_border
        (vandermonde_le_symmetric (hordinary_to_vandermonde ho)),
      fun hb => hvandermonde_to_ordinary
        (vandermondeRankAtMost_mono
          (hl q (symmetric_border_le_ordinary_border hm hb)) hu)⟩
  · exact ⟨hordinary_to_vandermonde, hvandermonde_to_ordinary⟩

/-- The full generic TR-13 target in the frozen statement's all-width form.
The polynomial witness describes a nonempty principal Zariski-open subset of
the original complex Hankel moment space. -/
theorem generic_width_equivalence (m n : ℕ) (hm : 5 ≤ m)
    (hodd : Odd m) (hn : 2 ≤ n) :
    ∃ p : MvPolynomial (Fin (m * (n - 1) + 1)) ℂ,
      (∃ h : Moments m n, MvPolynomial.eval h p ≠ 0) ∧
      ∀ h : Moments m n, MvPolynomial.eval h p ≠ 0 →
        EqualFiveWidths (hankel h) := by
  obtain ⟨p, hp, hu⟩ := generic_vandermonde_upper m n hm hodd hn
  obtain ⟨q, hq, hl⟩ := generic_border_lower m n hm hodd hn
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  refine ⟨p * q, ?_, ?_⟩
  · obtain ⟨h, hh⟩ := principalOpen_nonempty hpq
    exact ⟨h, hh⟩
  · intro h hh
    rw [map_mul] at hh
    obtain ⟨hph, hqh⟩ := mul_ne_zero_iff.mp hh
    exact equalFiveWidths_of_bounds (by omega) (hu h hph) (hl h hqh)

#assert_trust kernel vandermondeRankAtMost_mono
#assert_trust kernel equalFiveWidths_of_bounds
#assert_trust kernel generic_width_equivalence
#print axioms generic_width_equivalence

end NLA.TR13
