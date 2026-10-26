import NLA.Proofs.TR06.RealAdditionProperness
import NLA.Proofs.TR06.FiniteLocalizedFibers
import NLA.TR06.FiniteFiberExactness

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open Set

namespace NLA.Proofs.TR06
open NLA.TR06 NLA.TR06.Proposed

variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- Finiteness concerns the COMPLETE actual complex fiber, retaining zero
summands. It is derived from finite localization and actual character tuples. -/
theorem closed_addition_fiber_finite (hd : 0 < d) (t : AdditionImage d n r)
    [Module.Finite (Localization.Away t)
      (Localization (Algebra.algebraMapSubmonoid (SegreSource d n r) (Submonoid.powers t)))]
    (A : Tensor ℂ d n) (hA : additionBaseValue t A ≠ 0) :
    (closedAdditionFiber r A).Finite := by
  classical
  by_cases hnon : (closedAdditionFiber r A).Nonempty
  · obtain ⟨a, ha⟩ := hnon
    have harange : a ∈ Set.range (characterTuple (d := d) (n := n) (r := r)) := by
      rw [range_characterTuple hd]
      exact ha.1
    obtain ⟨f, hf⟩ := harange
    let χ : AdditionImage d n r →ₐ[ℂ] ℂ := f.comp (additionAlgebraHom d n r).range.val
    have hχ : χ t ≠ 0 := by
      change f t.val ≠ 0
      rw [← additionBaseValue_characterTuple t f, hf, ha.2]
      exact hA
    have hfinite := finite_character_fiber_of_finite_localization (S := SegreSource d n r) t χ hχ
    apply (hfinite.image (characterTuple (d := d) (n := n) (r := r))).subset
    intro b hb
    have hbrange : b ∈ Set.range (characterTuple (d := d) (n := n) (r := r)) := by
      rw [range_characterTuple hd]
      exact hb.1
    obtain ⟨g, hg⟩ := hbrange
    refine ⟨g, ?_, hg⟩
    change g.comp (IsScalarTower.toAlgHom ℂ (AdditionImage d n r) (SegreSource d n r)) = χ
    ext c
    change g c.val = f c.val
    rw [← additionBaseValue_characterTuple c g, ← additionBaseValue_characterTuple c f,
      hg, hf, hb.2, ha.2]
  · rw [Set.not_nonempty_iff_eq_empty.mp hnon]
    exact Set.finite_empty

/-- A real length-r decomposition over the good base has complex exact rank r;
lower complex rank would create the retained infinite splitting/cancellation
families in the complete fiber, contradicting proved finite localization. -/
theorem complex_exactRank_on_real_good_base (hd : 0 < d) (hn : ∀ j, 0 < n j)
    (hr : 2 ≤ r) (t : AdditionImage d n r)
    [Module.Finite (Localization.Away t)
      (Localization (Algebra.algebraMapSubmonoid (SegreSource d n r) (Submonoid.powers t)))]
    (A : Tensor ℝ d n) (hA : A ∈ realAdditionGoodSet t)
    (hdec : ∃ a : Fin r → Tensor ℝ d n, Decomposes a A) :
    ExactRank r (complexify A) := by
  obtain ⟨a, ha⟩ := hdec
  have hca := complexify_decomposes ha
  apply FiniteFiber.exact_rank_statement ℂ d n r hd hn hr (complexify A)
    (closed_addition_fiber_finite hd t (complexify A) hA)
  exact ⟨fun i => complexify (a i), (fun i => Or.inr (hca.1 i)), hca.2⟩

#print axioms closed_addition_fiber_finite
#print axioms complex_exactRank_on_real_good_base
#assert_trust kernel closed_addition_fiber_finite
#assert_trust kernel complex_exactRank_on_real_good_base

end NLA.Proofs.TR06
