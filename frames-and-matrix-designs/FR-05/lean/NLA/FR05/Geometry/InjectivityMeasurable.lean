import NLA.FR05.Definitions
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.LocallyClosed

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace NLA.FR05

theorem isClosed_globallyPhased (d : ℕ) :
    IsClosed {p : Signal d × Signal d | GloballyPhased p.1 p.2} := by
  let U := Metric.sphere (0 : ℂ) 1
  have hu : IsCompact U := isCompact_sphere _ _
  let _ : CompactSpace U := isCompact_iff_compactSpace.mp hu
  let S : Set ((Signal d × Signal d) × U) :=
    {p | p.1.2 = (p.2 : ℂ) • p.1.1}
  have hs : IsClosed S := isClosed_eq (by fun_prop) (by fun_prop)
  have he : {p : Signal d × Signal d | GloballyPhased p.1 p.2} = Prod.fst '' S := by
    ext p
    constructor
    · rintro ⟨θ, hθ⟩
      have hc : Complex.exp (θ * Complex.I) ∈ U := by
        change Complex.exp (θ * Complex.I) ∈ Metric.sphere 0 1
        rw [← Complex.range_exp_mul_I]
        exact ⟨θ, rfl⟩
      exact ⟨(p, ⟨_, hc⟩), hθ, rfl⟩
    · rintro ⟨⟨q, c⟩, hq, rfl⟩
      have hc : (c : ℂ) ∈ Set.range (fun θ : ℝ ↦ Complex.exp (θ * Complex.I)) := by
        rw [Complex.range_exp_mul_I]
        exact c.property
      obtain ⟨θ, hθ⟩ := hc
      exact ⟨θ, by change q.2 = _; simpa only [S, Set.mem_ofPred_eq, hθ] using hq⟩
  rw [he]
  exact isClosedMap_fst_of_compactSpace S hs

theorem measurableSet_phaseRetrievalInjective (m d : ℕ) :
    MeasurableSet {A : Fin m → Signal d | PhaseRetrievalInjective A} := by
  let W : Set ((Fin m → Signal d) × Signal d × Signal d) :=
    {p | SameMeasurements p.1 p.2.1 p.2.2 ∧ ¬ GloballyPhased p.2.1 p.2.2}
  have hm : IsClosed {p : (Fin m → Signal d) × Signal d × Signal d |
      SameMeasurements p.1 p.2.1 p.2.2} := by
    unfold SameMeasurements
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_eq (by unfold rowMagnitude; fun_prop) (by unfold rowMagnitude; fun_prop)
  have hp : IsOpen {p : (Fin m → Signal d) × Signal d × Signal d |
      ¬ GloballyPhased p.2.1 p.2.2} :=
    ((isClosed_globallyPhased d).preimage continuous_snd).isOpen_compl
  have hw : IsLocallyClosed W := hm.isLocallyClosed.inter hp.isLocallyClosed
  let _ : LocallyCompactSpace W := hw.locallyCompactSpace
  have hc : IsSigmaCompact (Prod.fst '' W) := by
    have h := isSigmaCompact_range (f := fun w : W ↦ w.val.1) (by fun_prop)
    have he : Set.range (fun w : W ↦ w.val.1) = Prod.fst '' W := by
      ext A
      simp
    rwa [he] at h
  have he : Prod.fst '' W = {A : Fin m → Signal d | ¬ PhaseRetrievalInjective A} := by
    ext A
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨B, x, y⟩, ⟨hxy, hn⟩, rfl⟩ h
      exact hn (h x y hxy)
    · intro h
      unfold PhaseRetrievalInjective at h
      push Not at h
      obtain ⟨x, y, hxy, hn⟩ := h
      exact ⟨(A, x, y), ⟨hxy, hn⟩, rfl⟩
  obtain ⟨K, hK, heK⟩ := hc
  have hb : MeasurableSet {A : Fin m → Signal d | ¬ PhaseRetrievalInjective A} := by
    rw [← he, ← heK]
    exact MeasurableSet.iUnion fun n ↦ (hK n).isClosed.measurableSet
  simpa only [Set.compl_ofPred, not_not] using hb.compl
end NLA.FR05
