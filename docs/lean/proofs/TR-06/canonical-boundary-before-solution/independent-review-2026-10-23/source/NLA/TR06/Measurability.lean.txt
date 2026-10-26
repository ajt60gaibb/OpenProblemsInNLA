/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.Definitions
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open Set MeasureTheory
namespace NLA.TR06

/-- A locally closed subset of a locally compact second-countable space has
Borel continuous image in a Hausdorff space, since that image is sigma compact. -/
private theorem measurableSet_image_locallyClosed
    {X Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] {s : Set X} (hs : IsLocallyClosed s)
    {f : X → Y} (hf : Continuous f) : MeasurableSet (f '' s) := by
  let : LocallyCompactSpace s := hs.locallyCompactSpace
  have hsc : IsSigmaCompact s := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  obtain ⟨K, hK, hcover⟩ := hsc.image hf
  rw [← hcover]
  exact MeasurableSet.iUnion (fun j => (hK j).isClosed.measurableSet)

private abbrev Factors (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :=
  Fin r → (j : Fin d) → Fin (n j) → ℝ

private def factorTuple {d r : ℕ} {n : Fin d → ℕ} (u : Factors d n r) :
    Fin r → Tensor ℝ d n := fun i => pureTensor (u i)

private def factorSum {d r : ℕ} {n : Fin d → ℕ} (u : Factors d n r) :
    Tensor ℝ d n := ∑ i, factorTuple u i

private def nonzeroFactors (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    Set (Factors d n r) := {u | ∀ i, factorTuple u i ≠ 0}

private theorem continuous_factorTuple {d r : ℕ} {n : Fin d → ℕ} (i : Fin r) :
    Continuous (fun u : Factors d n r => factorTuple u i) := by
  unfold factorTuple pureTensor
  apply (PiLp.continuous_toLp 2 (fun _ : TensorIndex d n => ℝ)).comp
  apply continuous_pi
  intro q
  exact continuous_finsetProd _ (fun j _ =>
    (continuous_apply (q j)).comp ((continuous_apply j).comp (continuous_apply i)))

private theorem continuous_factorSum {d r : ℕ} {n : Fin d → ℕ} :
    Continuous (factorSum (d := d) (n := n) (r := r)) := by
  exact continuous_finsetSum _ (fun i _ => continuous_factorTuple i)

private theorem isOpen_nonzeroFactors (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    IsOpen (nonzeroFactors d n r) := by
  change IsOpen {u : Factors d n r | ∀ i, factorTuple u i ≠ 0}
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact (isClosed_eq (continuous_factorTuple i) continuous_const).isOpen_compl

private theorem factorSum_image_nonzeroFactors (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    factorSum '' nonzeroFactors d n r =
      {A : Tensor ℝ d n | ∃ a : Fin r → Tensor ℝ d n, Decomposes a A} := by
  classical
  ext A
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨factorTuple u, fun i => ⟨hu i, u i, rfl⟩, rfl⟩
  · rintro ⟨a, ha, hsum⟩
    choose u hu using fun i => (ha i).2
    have heq : factorTuple u = a := funext hu
    refine ⟨u, ?_, ?_⟩
    · intro i
      simpa only [heq] using (ha i).1
    · simpa only [factorSum, heq] using hsum

/-- The real locus admitting exactly this many nonzero pure summands is Borel;
this is not a claim about minimal tensor rank. -/
theorem measurableSet_decomposable (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    MeasurableSet {A : Tensor ℝ d n | ∃ a : Fin r → Tensor ℝ d n, Decomposes a A} := by
  rw [← factorSum_image_nonzeroFactors]
  exact measurableSet_image_locallyClosed
    (isOpen_nonzeroFactors d n r).isLocallyClosed continuous_factorSum

/-- The exact-rank locus is Borel without a genericity hypothesis. -/
theorem measurableSet_exactRank (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    MeasurableSet {A : Tensor ℝ d n | ExactRank r A} := by
  change MeasurableSet ({A | ∃ a : Fin r → Tensor ℝ d n, Decomposes a A} ∩
    {A | ∀ m < r, ¬ ∃ a : Fin m → Tensor ℝ d n, Decomposes a A})
  apply (measurableSet_decomposable d n r).inter
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
    (measurableSet_decomposable d n m).compl

private def disagreeingFactors (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    Set (Factors d n r × Factors d n r) :=
  {uv | uv.1 ∈ nonzeroFactors d n r ∧ uv.2 ∈ nonzeroFactors d n r ∧
    ∀ σ : Equiv.Perm (Fin r), ¬ ∀ i, factorTuple uv.2 i = factorTuple uv.1 (σ i)}

private def equalSumFactors (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    Set (Factors d n r × Factors d n r) :=
  {uv | factorSum uv.1 = factorSum uv.2}

private theorem isOpen_disagreeingFactors (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    IsOpen (disagreeingFactors d n r) := by
  change IsOpen ((Prod.fst ⁻¹' nonzeroFactors d n r) ∩
    ((Prod.snd ⁻¹' nonzeroFactors d n r) ∩
      {uv | ∀ σ : Equiv.Perm (Fin r), ¬ ∀ i,
        factorTuple uv.2 i = factorTuple uv.1 (σ i)}))
  apply ((isOpen_nonzeroFactors d n r).preimage continuous_fst).inter
  apply ((isOpen_nonzeroFactors d n r).preimage continuous_snd).inter
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro σ
  have hc : IsClosed {uv : Factors d n r × Factors d n r |
      ∀ i, factorTuple uv.2 i = factorTuple uv.1 (σ i)} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq
      ((continuous_factorTuple i).comp continuous_snd)
      ((continuous_factorTuple (σ i)).comp continuous_fst)
  exact hc.isOpen_compl

private theorem isClosed_equalSumFactors (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    IsClosed (equalSumFactors d n r) := by
  exact isClosed_eq (continuous_factorSum.comp continuous_fst)
    (continuous_factorSum.comp continuous_snd)

private theorem factorSum_image_nonidentifiable (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    (fun uv : Factors d n r × Factors d n r => factorSum uv.1) ''
      (equalSumFactors d n r ∩ disagreeingFactors d n r) =
      {A : Tensor ℝ d n | ¬ Identifiable r A} := by
  classical
  ext A
  constructor
  · rintro ⟨⟨u, v⟩, ⟨heq, hu, hv, hdis⟩, rfl⟩ hident
    obtain ⟨σ, hσ⟩ := hident (factorTuple u) (factorTuple v)
      ⟨fun i => ⟨hu i, u i, rfl⟩, rfl⟩
      ⟨fun i => ⟨hv i, v i, rfl⟩, heq.symm⟩
    exact hdis σ hσ
  · intro hident
    simp only [Identifiable, not_forall, not_exists] at hident
    obtain ⟨a, b, ha, hb, hdis⟩ := hident
    choose u hu using fun i => (ha.1 i).2
    choose v hv using fun i => (hb.1 i).2
    have hueq : factorTuple u = a := funext hu
    have hveq : factorTuple v = b := funext hv
    refine ⟨(u, v), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · change factorSum u = factorSum v
      simpa only [factorSum, hueq, hveq] using ha.2.trans hb.2.symm
    · intro i
      simpa only [hueq] using (ha.1 i).1
    · intro i
      simpa only [hveq] using (hb.1 i).1
    · simpa only [hueq, hveq, not_forall] using hdis
    · simpa only [factorSum, hueq] using ha.2

/-- Failure of uniqueness up to permutation is Borel, using two actual
nonzero factor tuples and every permutation, including in degenerate formats. -/
theorem measurableSet_nonidentifiable (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    MeasurableSet {A : Tensor ℝ d n | ¬ Identifiable r A} := by
  rw [← factorSum_image_nonidentifiable]
  exact measurableSet_image_locallyClosed
    ((isClosed_equalSumFactors d n r).isLocallyClosed.inter
      (isOpen_disagreeingFactors d n r).isLocallyClosed)
    (continuous_factorSum.comp continuous_fst)

/-- The full frozen sampling locus is Borel. This statement supplies no
regularity, dimension, induced-volume nullity, or integrability assumption. -/
theorem measurableSet_identifiableRealSet (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    MeasurableSet (identifiableRealSet d n r) := by
  classical
  have h := (measurableSet_exactRank d n r).diff (measurableSet_nonidentifiable d n r)
  convert h using 1
  ext A
  simp [identifiableRealSet]

#print axioms measurableSet_decomposable
#print axioms measurableSet_exactRank
#print axioms measurableSet_nonidentifiable
#print axioms measurableSet_identifiableRealSet
#assert_trust kernel measurableSet_decomposable
#assert_trust kernel measurableSet_exactRank
#assert_trust kernel measurableSet_nonidentifiable
#assert_trust kernel measurableSet_identifiableRealSet
end NLA.TR06
