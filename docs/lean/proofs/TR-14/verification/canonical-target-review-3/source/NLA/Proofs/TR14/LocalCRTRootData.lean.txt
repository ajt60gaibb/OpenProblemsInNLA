import NLA.Proofs.TR14.LocalFourierMode
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
Exact complex root data for a monic positive-degree polynomial, retaining
every multiplicity. This is the first CRT gate; no quotient equivalence or
global tensor width is asserted here.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial
open scoped BigOperators Polynomial
noncomputable section

/-- Distinct roots of `g`, represented without dropping their later counts. -/
def localRootSupport (g : Polynomial ℂ) : Finset ℂ := g.roots.toFinset

/-- The finite index type of distinct complex roots. -/
abbrev LocalRootIndex (g : Polynomial ℂ) := localRootSupport g

/-- The exact multiplicity of one indexed root. -/
def localRootMultiplicity (g : Polynomial ℂ) (α : LocalRootIndex g) : ℕ :=
  g.roots.count α.val

theorem localRootMultiplicity_pos (g : Polynomial ℂ)
    (α : LocalRootIndex g) : 0 < localRootMultiplicity g α := by
  classical
  apply Multiset.count_pos.mpr
  exact (Multiset.mem_toFinset.mp α.property)

/-- The sum of all positive multiplicities is exactly the monic degree. -/
theorem localRootMultiplicity_sum (g : Polynomial ℂ) :
    (∑ α : LocalRootIndex g, localRootMultiplicity g α) = g.natDegree := by
  classical
  calc
    (∑ α : LocalRootIndex g, localRootMultiplicity g α) =
        ∑ α ∈ localRootSupport g, g.roots.count α := by
          change (∑ α ∈ (localRootSupport g).attach, g.roots.count α.val) =
            ∑ α ∈ localRootSupport g, g.roots.count α
          exact Finset.sum_attach (localRootSupport g)
            (fun α : ℂ => g.roots.count α)
    _ = g.roots.card := Multiset.toFinset_sum_count_eq g.roots
    _ = g.natDegree := IsAlgClosed.card_roots_eq_natDegree

/-- A positive-degree monic polynomial has at least one distinct root. -/
theorem localRootSupport_nonempty (g : Polynomial ℂ)
    (_hg : g.Monic) (hr : 0 < g.natDegree) :
    (localRootSupport g).Nonempty := by
  classical
  by_contra hnone
  have hzero : localRootSupport g = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
  have hsum : (∑ α ∈ localRootSupport g, g.roots.count α) = g.natDegree :=
    (Multiset.toFinset_sum_count_eq g.roots).trans
      IsAlgClosed.card_roots_eq_natDegree
  rw [hzero] at hsum
  simp at hsum
  omega

/-- Complete factorization over `ℂ`, with one factor per distinct root and
its exact multiplicity. -/
theorem localRoot_factorization (g : Polynomial ℂ) (hg : g.Monic) :
    g = ∏ α ∈ localRootSupport g,
      ((Polynomial.X : Polynomial ℂ) - Polynomial.C α) ^ g.roots.count α := by
  classical
  calc
    g = (g.roots.map fun α : ℂ =>
          (Polynomial.X : Polynomial ℂ) - Polynomial.C α).prod :=
      (IsAlgClosed.splits g).eq_prod_roots_of_monic hg
    _ = ∏ α ∈ localRootSupport g,
          ((Polynomial.X : Polynomial ℂ) - Polynomial.C α) ^ g.roots.count α := by
      simpa only [localRootSupport] using
        (Finset.prod_multiset_map_count g.roots
          (fun α : ℂ => (Polynomial.X : Polynomial ℂ) - Polynomial.C α))

/-- Distinct indexed roots yield pairwise coprime powers of their exact
linear factors. This is the polynomial input to the ideal CRT. -/
theorem localRootFactors_pairwise_coprime (g : Polynomial ℂ) :
    Pairwise (fun α β : LocalRootIndex g =>
      IsCoprime
        (((Polynomial.X : Polynomial ℂ) - Polynomial.C α.val) ^
          localRootMultiplicity g α)
        (((Polynomial.X : Polynomial ℂ) - Polynomial.C β.val) ^
          localRootMultiplicity g β)) := by
  classical
  intro α β hne
  have hαβ : α.val ≠ β.val := by
    intro heq
    exact hne (Subtype.ext heq)
  exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    ((sub_ne_zero.mpr hαβ).isUnit)).pow

#assert_trust kernel localRootMultiplicity_pos
#assert_trust kernel localRootMultiplicity_sum
#assert_trust kernel localRootSupport_nonempty
#assert_trust kernel localRoot_factorization
#assert_trust kernel localRootFactors_pairwise_coprime
#print axioms localRoot_factorization

end
end NLA.Proofs.TR14
