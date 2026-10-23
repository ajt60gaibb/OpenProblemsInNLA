import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Compactness.Compact
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped NNReal
open Set

namespace NLA.Proofs.TR06

/-- The actual Cauchy root bound for a monic polynomial with bounded coefficients. -/
theorem monic_root_bound {p : Polynomial ℂ} (hp : p.Monic) {z : ℂ}
    (hz : p.IsRoot z) (M : ℝ≥0)
    (hM : ∀ j < p.natDegree, ‖p.coeff j‖₊ ≤ M) :
    ‖z‖₊ ≤ M + 1 := by
  have hsup : (Finset.range p.natDegree).sup (fun j => ‖p.coeff j‖₊) ≤ M := by
    exact Finset.sup_le fun j hj => hM j (Finset.mem_range.mp hj)
  have hb := hz.norm_lt_cauchyBound hp.ne_zero
  have hc : p.cauchyBound ≤ M + 1 := by
    simpa [Polynomial.cauchyBound, hp.leadingCoeff] using add_le_add_right hsup 1
  exact hb.le.trans hc

/-- Continuous coefficients on a compact base give a uniform bound for every
root of every polynomial in the specified finite coordinate family. This is a
support lemma; constructing the actual finite-localization monic relations is
a separate obligation. -/
theorem compact_monic_root_bound {Y ι : Type*} [TopologicalSpace Y] [Fintype ι]
    (K : Set Y) (hK : IsCompact K) (P : Y → ι → Polynomial ℂ) (N : ℕ)
    (hmonic : ∀ y ∈ K, ∀ i, (P y i).Monic)
    (hdegree : ∀ y ∈ K, ∀ i, (P y i).natDegree ≤ N)
    (hcoeff : ∀ i (j : Fin N), ContinuousOn (fun y => (P y i).coeff j) K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ K, ∀ i z, (P y i).IsRoot z → ‖z‖ ≤ B := by
  classical
  let g : Y → (ι × Fin N → ℂ) := fun y ij => (P y ij.1).coeff ij.2
  have hg : ContinuousOn g K := by
    apply continuousOn_pi.mpr
    intro ij
    exact hcoeff ij.1 ij.2
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg
  let M : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  refine ⟨M + 1, by positivity, ?_⟩
  intro y hy i z hz
  have hb := monic_root_bound (hmonic y hy i) hz M (by
    intro j hj
    have hjN : j < N := lt_of_lt_of_le hj (hdegree y hy i)
    have hcoord : ‖(P y i).coeff j‖ ≤ max C 0 :=
      (norm_le_pi_norm (g y) (i, ⟨j, hjN⟩)).trans ((hC y hy).trans (le_max_left _ _))
    exact_mod_cast hcoord)
  exact_mod_cast hb

/-- A closed source whose actual coordinates satisfy monic equations over its
image has compact complete preimages above compact bases. Zero coordinates and
all source branches are included; no cancellation-escape exclusion is assumed.
The monic relations and their continuous coefficients must be constructed
before this lemma can establish actual addition properness. -/
theorem compact_preimage_of_monic_coordinates {E Y ι : Type*}
    [TopologicalSpace E] [T2Space E] [TopologicalSpace Y] [T2Space Y] [Fintype ι]
    (e : E ≃ₜ (ι → ℂ)) (f : E → Y) (hf : Continuous f)
    (C : Set E) (hC : IsClosed C) (K : Set Y) (hK : IsCompact K)
    (P : Y → ι → Polynomial ℂ) (N : ℕ)
    (hmonic : ∀ y ∈ K, ∀ i, (P y i).Monic)
    (hdegree : ∀ y ∈ K, ∀ i, (P y i).natDegree ≤ N)
    (hcoeff : ∀ i (j : Fin N), ContinuousOn (fun y => (P y i).coeff j) K)
    (hrelations : ∀ a ∈ C, f a ∈ K → ∀ i, (P (f a) i).IsRoot (e a i)) :
    IsCompact {a | a ∈ C ∧ f a ∈ K} := by
  classical
  obtain ⟨B, _hB, hbound⟩ := compact_monic_root_bound K hK P N hmonic hdegree hcoeff
  let box : Set (ι → ℂ) := Set.pi Set.univ (fun _ => Metric.closedBall 0 B)
  have hbox : IsCompact box := by
    have heq : box = {x : ι → ℂ | ∀ i, x i ∈ Metric.closedBall 0 B} := by
      ext x
      simp only [box, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_ofPred_eq]
    rw [heq]
    exact isCompact_pi_infinite (fun _ : ι => isCompact_closedBall (0 : ℂ) B)
  have hclosed : IsClosed {a | a ∈ C ∧ f a ∈ K} := hC.inter (hK.isClosed.preimage hf)
  apply (hbox.image e.symm.continuous).of_isClosed_subset hclosed
  intro a ha
  refine ⟨e a, ?_, e.symm_apply_apply a⟩
  intro i _hi
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    hbound (f a) ha.2 i (e a i) (hrelations a ha.1 ha.2 i)

#print axioms monic_root_bound
#print axioms compact_monic_root_bound
#print axioms compact_preimage_of_monic_coordinates
#assert_trust kernel monic_root_bound
#assert_trust kernel compact_monic_root_bound
#assert_trust kernel compact_preimage_of_monic_coordinates

end NLA.Proofs.TR06
