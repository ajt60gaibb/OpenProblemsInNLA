/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original TR-06 mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.AdditionLocalizationDefinitions
import NLA.TR06.FiniteCharacterFiber
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open Set
namespace NLA.TR06.Proposed

/-- One actual complex identifiable exact-rank tensor supplies generic
quasi-finiteness and a nonzero finite localization of actual addition. -/
theorem addition_finite_localization : AdditionFiniteLocalizationStatement := by
  classical
  intro d n r hd ⟨A, hrank, hident⟩
  let S := SegreSource d n r
  let R := AdditionImage d n r
  let : Algebra.FiniteType ℂ S := (segre_algebra_structure d n r).2
  obtain ⟨a, ha⟩ := hrank.1
  have hac : a ∈ closedRankOneProduct ℂ d n r := fun i => Or.inr (ha.1 i)
  have haf : a ∈ Set.range (characterTuple (d := d) (n := n) (r := r)) := by
    rw [range_characterTuple hd]
    exact hac
  obtain ⟨f, hf⟩ := haf
  let χ : R →ₐ[ℂ] ℂ := f.comp (additionAlgebraHom d n r).range.val
  have hsum (g : S →ₐ[ℂ] ℂ) (hg : g ∈ characterFiber (K := ℂ) (R := R) (S := S) χ) :
      (∑ i, characterTuple g i) = A := by
    have hgf : (∑ i, characterTuple g i) = ∑ i, characterTuple f i := by
      ext q
      let v : R := ⟨additionAlgebraHom d n r (MvPolynomial.X q), ⟨MvPolynomial.X q, rfl⟩⟩
      have hv := DFunLike.congr_fun hg v
      change g (additionAlgebraHom d n r (MvPolynomial.X q)) =
        f (additionAlgebraHom d n r (MvPolynomial.X q)) at hv
      simpa [additionAlgebraHom, characterTuple] using hv
    rw [hgf, hf, ha.2]
  have hfinite : (characterFiber (K := ℂ) (R := R) (S := S) χ).Finite := by
    have hpre := Set.Finite.preimage
      (characterTuple_injective (d := d) (n := n) (r := r)).injOn
      (closedAdditionFiber_finite_nonempty hrank hident).1
    apply hpre.subset
    intro g hg
    exact ⟨characterTuple_mem_closedProduct hd g, hsum g hg⟩
  have hnonempty : (characterFiber (K := ℂ) (R := R) (S := S) χ).Nonempty := by
    exact ⟨f, rfl⟩
  have hqf : Algebra.QuasiFiniteAt R (⊥ : Ideal S) :=
    generic_quasiFinite_of_finite_nonempty_character_fiber ℂ R S χ hfinite hnonempty
  let : Algebra.FiniteType R S := Algebra.FiniteType.of_restrictScalars_finiteType ℂ R S
  exact ⟨hqf, generic_finite_localization R S Subtype.val_injective hqf⟩

#print axioms addition_finite_localization
#assert_trust kernel addition_finite_localization
end NLA.TR06.Proposed
