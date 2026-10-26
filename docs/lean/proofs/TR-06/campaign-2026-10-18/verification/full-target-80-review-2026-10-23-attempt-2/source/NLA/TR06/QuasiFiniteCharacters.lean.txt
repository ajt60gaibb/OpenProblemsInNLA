/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.

Exact intermediate statements were independently reviewed before implementation.
This bounds algebraic characters, not yet the normalized tensor graph fibers.
-/
import NLA.TR06.QuasiFiniteCharactersDefinitions
import NLA.TR06.AlgebraFiber

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Function Set TopologicalSpace

namespace NLA.TR06.Proposed

/-- A character on an away localization is determined by its restriction to the
finite envelope whenever its denominator value is nonzero. -/
theorem away_character_restriction : AwayCharacterRestrictionStatement := by
  intro R S K _ _ _ _ _ A r hsurj f hf g _hg hfg
  ext s
  obtain ⟨b, n, hb⟩ := Localization.awayMap_surjective_iff.mp hsurj s
  change b.val = r.val ^ n * s at hb
  have hr : f r.val = g r.val := congrArg (fun h : A →ₐ[R] K => h r) hfg
  have hbg : f b.val = g b.val := congrArg (fun h : A →ₐ[R] K => h b) hfg
  have hmul : (f r.val)^n * f s = (f r.val)^n * g s := by
    calc
      _ = f b.val := by rw [hb, map_mul, map_pow]
      _ = g b.val := hbg
      _ = _ := by rw [hb, map_mul, map_pow, ← hr]
  exact mul_left_cancel₀ (pow_ne_zero n hf) hmul

/-- Finite-type source characters at quasi-finite primes have a single finite
bound independent of the target field's R-algebra action. -/
theorem uniform_quasiFinite_character_bound : UniformQuasiFiniteCharacterBoundStatement := by
  classical
  intro R S K _ _ _ _ _ _
  let Q : Set (PrimeSpectrum S) := {p | Algebra.QuasiFiniteAt R p.asIdeal}
  have hexists (p : Q) : ∃ A : Subalgebra R S, A.toSubmodule.FG ∧ ∃ r : A,
      r.val ∉ p.val.asIdeal ∧ Function.Bijective (Localization.awayMap A.val.toRingHom r) := by
    let : Algebra.QuasiFiniteAt R p.val.asIdeal := p.property
    exact Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective p.val.asIdeal
  choose A hA r hr hbij using hexists
  let U : Q → Set (PrimeSpectrum S) := fun p => PrimeSpectrum.basicOpen (r p).val
  obtain ⟨I, hI⟩ := (NoetherianSpace.isCompact Q).elim_finite_subcover U
    (fun _ => PrimeSpectrum.isOpen_basicOpen) (by
      intro p hp
      refine mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
      exact (PrimeSpectrum.mem_basicOpen _ _).mpr (hr ⟨p, hp⟩))
  have hgen (p : Q) : ∃ n : ℕ, ∃ g : Fin n → A p,
      Submodule.span R (Set.range g) = ⊤ := by
    let : Module.Finite R (A p) := ⟨(Submodule.fg_top (A p).toSubmodule).mpr (hA p)⟩
    exact Module.Finite.exists_fin
  choose n gen hgen using hgen
  refine ⟨∑ p ∈ I, n p, ?_⟩
  intro aK
  let := aK
  intro q hq
  let t : Q → Finset (S →ₐ[R] K) := fun p => q.filter (fun f => f (r p).val ≠ 0)
  have htcard (p : Q) : (t p).card ≤ n p := by
    have hinj : Set.InjOn (fun f : S →ₐ[R] K => f.comp (A p).val) (↑(t p) : Set (S →ₐ[R] K)) :=
      (away_character_restriction R S K (A p) (r p) (hbij p).surjective).mono
        (fun f hf => (Finset.mem_filter.mp hf).2)
    rw [← Finset.card_image_of_injOn hinj]
    exact NLA.TR06.card_algHom_finset_le_of_span_eq_top (gen p) (hgen p) _
  have hcover : q ⊆ I.biUnion t := by
    intro f hf
    have hker : characterPrime f ∈ Q := hq f hf
    obtain ⟨p, hp, hU⟩ := mem_iUnion₂.mp (hI hker)
    have hnonzero : f (r p).val ≠ 0 := by
      have H := (PrimeSpectrum.mem_basicOpen (r p).val (characterPrime f)).mp hU
      change (r p).val ∉ RingHom.ker f.toRingHom at H
      exact fun hz => H (RingHom.mem_ker.mpr hz)
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hf, hnonzero⟩⟩
  calc
    q.card ≤ (I.biUnion t).card := Finset.card_le_card hcover
    _ ≤ ∑ p ∈ I, (t p).card := Finset.card_biUnion_le
    _ ≤ ∑ p ∈ I, n p := Finset.sum_le_sum fun p _ => htcard p

#print axioms away_character_restriction
#print axioms uniform_quasiFinite_character_bound
#assert_trust kernel away_character_restriction
#assert_trust kernel uniform_quasiFinite_character_bound

end NLA.TR06.Proposed
