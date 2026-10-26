import NLA.Proofs.TR14.UnitSpan
import Mathlib.Algebra.Module.Submodule.Union

/-! A unit can avoid finitely many proper linear subspaces of a
one-containing space. This supplies a direct finite-subspace version of the
repeated-parameter argument in the contextual product inequality. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

variable {K B : Type*} [Field K] [CommRing B] [Algebra K B]

/-- A scalar line through a point outside a subspace meets it at most once. -/
theorem scalar_line_hits_subsingleton (P : Submodule K B) (x : B) (hx : x ∉ P) :
    Set.Subsingleton {c : K | x + c • (1 : B) ∈ P} := by
  intro c hc d hd
  by_contra hcd
  have hsub : (c - d) • (1 : B) ∈ P := by
    convert P.sub_mem hc hd using 1; module
  have hone : (1 : B) ∈ P := (P.smul_mem_iff (sub_ne_zero.mpr hcd)).mp hsub
  have hxP : x ∈ P := by
    convert P.sub_mem hc (P.smul_mem c hone) using 1; module
  exact hx hxP

/-- No finite collection of proper subspaces can cover the actual units in
`U`. No assumption about reducedness or finiteness of subalgebras is used. -/
theorem exists_unit_avoiding_finite_subspaces [Infinite K] [FiniteDimensional K B]
    {ι : Type*} [Finite ι]
    (U : Submodule K B) (hU : (1 : B) ∈ U) (P : ι → Submodule K B)
    (hproper : ∀ i, ¬ U ≤ P i) :
    ∃ x ∈ U, IsUnit x ∧ ∀ i, x ∉ P i := by
  classical
  let Q (i : ι) : Submodule K U := (P i).comap U.subtype
  have hQ : ∀ i, Q i ≠ ⊤ := by
    intro i hi
    apply hproper i
    intro x hx
    have : (⟨x, hx⟩ : U) ∈ Q i := hi ▸ Submodule.mem_top
    exact this
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top Q hQ
  have hbad : (⋃ i, {c : K | (x : B) + c • (1 : B) ∈ P i}).Finite :=
    Set.finite_iUnion fun i => (scalar_line_hits_subsingleton (P i) x (hx i)).finite
  have hs := (algebra_finite_spectrum (K := K) (-(x : B))).union hbad
  obtain ⟨c, hc⟩ := hs.exists_notMem
  have hcunit : IsUnit ((x : B) + c • (1 : B)) := by
    have hc' : c ∉ spectrum K (-(x : B)) := fun h => hc (Or.inl h)
    simpa only [sub_neg_eq_add, Algebra.algebraMap_eq_smul_one, add_comm] using
      spectrum.notMem_iff.mp hc'
  refine ⟨(x : B) + c • (1 : B), U.add_mem x.property (U.smul_mem c hU), hcunit, ?_⟩
  intro i hi
  exact hc (Or.inr (Set.mem_iUnion.mpr ⟨i, hi⟩))

/-- If finitely many classes cover all units of `U`, one class spans `U`.
This is the precise replacement for choosing many equal auxiliary algebras
along a Vandermonde curve. -/
theorem exists_unit_class_spans [Infinite K] [FiniteDimensional K B]
    {ι : Type*} [Finite ι]
    (U : Submodule K B) (hU : (1 : B) ∈ U) (classes : ι → Set B)
    (hclasses : ∀ i x, x ∈ classes i → x ∈ U)
    (hcover : ∀ x ∈ U, IsUnit x → ∃ i, x ∈ classes i) :
    ∃ i, Submodule.span K (classes i) = U := by
  classical
  by_contra hnone
  push Not at hnone
  have hproper : ∀ i, ¬ U ≤ Submodule.span K (classes i) := by
    intro i hi
    exact hnone i (le_antisymm (Submodule.span_le.mpr (hclasses i)) hi)
  obtain ⟨x, hx, hunit, havoid⟩ :=
    exists_unit_avoiding_finite_subspaces U hU (fun i => Submodule.span K (classes i)) hproper
  obtain ⟨i, hi⟩ := hcover x hx hunit
  exact havoid i (Submodule.subset_span hi)

#assert_trust kernel exists_unit_avoiding_finite_subspaces
#assert_trust kernel exists_unit_class_spans
#print axioms exists_unit_class_spans

end NLA.Proofs.TR14
