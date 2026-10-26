import NLA.Proofs.TR04.TTStrictOriginalView
import NLA.Proofs.TR04.TTStrictExplicitFamily

/-! The strict mathematical construction at the immutable original tensor,
rank, squared-error and actual sInf optimum boundary. The finite RAM program
and its operation count are separate obligations. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04.TensorFormat.TTStrict.Original
open NLA.Computation.TensorTrainApproximation NLA.Computation.SVDMachine

theorem output_minimum_iff {S : Shape} {ms : List ℕ} (hl : modeList S.mode = ms)
    {ι : Type*} (A : NLA.Computation.TensorTrainApproximation.Tensor S)
    (X : ι → TensorFormat.Tensor ms) (imin : ι) :
    IsMinimum (input hl A) X imin ↔
      ∀ j, FrobeniusSq S A (output hl (X imin)) ≤ FrobeniusSq S A (output hl (X j)) := by
  simp only [IsMinimum, output_error]

set_option maxHeartbeats 800000 in
/-- The deterministic explicit cyclic/prefix family at the exact original
Feasible, FrobeniusSq and actual sInf Optimum boundary. Every actual first SVD,
child-completion family and actual error-minimizing candidate is retained. -/
theorem first_svd_explicit_strict_family (S : Shape) (r : Ranks S) (hr : ∀ j, 1 ≤ r j)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S)
    {m n : ℕ} {ns : List ℕ} (hl : modeList S.mode = m :: n :: ns)
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m (suffixSize (n :: ns))) → ℝ}
    {V : Matrix (Fin (suffixSize (n :: ns))) (Fin (suffixSize (n :: ns))) ℝ}
    (h : ValidSVD (denseFirst (input hl A)) U sigma V) :
    let F := explicitFirstFrames h (originalRanks S r 0)
    F.count ≤ min m (suffixSize (n :: ns)) + 1 ∧ F.width ≤ min m (suffixSize (n :: ns)) ∧
      (∃ Z : Fin F.count → TensorFormat.Tensor ((F.width * n) :: ns),
        ∀ j, Completion ((F.width * n) :: ns) (fun i => originalRanks S r (i + 1))
          (merge F.width n ns (contract (F.frame j) (input hl A))) (Z j)) ∧
      ∀ Z : Fin F.count → TensorFormat.Tensor ((F.width * n) :: ns),
        (∀ j, Completion ((F.width * n) :: ns) (fun i => originalRanks S r (i + 1))
          (merge F.width n ns (contract (F.frame j) (input hl A))) (Z j)) →
        (∃ imin, (∀ j, FrobeniusSq S A (output hl (completionOutput (F.frame imin) (Z imin))) ≤
          FrobeniusSq S A (output hl (completionOutput (F.frame j) (Z j))))) ∧
        ∀ imin, (∀ j, FrobeniusSq S A (output hl (completionOutput (F.frame imin) (Z imin))) ≤
          FrobeniusSq S A (output hl (completionOutput (F.frame j) (Z j)))) →
          Feasible S r (output hl (completionOutput (F.frame imin) (Z imin))) ∧
          (0 < Optimum S r A →
            FrobeniusSq S A (output hl (completionOutput (F.frame imin) (Z imin))) <
              ((S.order : ℝ) - 1) * Optimum S r A) ∧
          (Optimum S r A = 0 → output hl (completionOutput (F.frame imin) (Z imin)) = A) := by
  dsimp only
  let F := explicitFirstFrames h (originalRanks S r 0)
  obtain ⟨hc, hw, hex, hall⟩ := explicit_strict_family (length_pos hl) (first_rank_pos S r hr) h
  refine ⟨hc, hw, hex, ?_⟩
  intro Z hZ
  obtain ⟨hminex, hminall⟩ := hall Z hZ
  refine ⟨?_, ?_⟩
  · obtain ⟨imin, hi⟩ := hminex
    exact ⟨imin, (output_minimum_iff hl A
      (fun j => completionOutput (F.frame j) (Z j)) imin).mp hi⟩
  intro imin hmin
  have hi := (output_minimum_iff hl A
    (fun j => completionOutput (F.frame j) (Z j)) imin).mpr hmin
  obtain ⟨hfeas, hcmp⟩ := hminall imin hi
  refine ⟨output_feasible hl r _ hfeas, ?_, ?_⟩
  · intro hpos
    obtain ⟨Y, hY, hopt⟩ := NLA.Proofs.TR04.exists_optimum S r A
    have hy := (input_feasible hl r Y).mp hY
    have he : error (m :: n :: ns) (input hl A) (input hl Y) = Optimum S r A :=
      (input_error hl A Y).symm.trans hopt.symm
    have hb := (hcmp (input hl Y) hy).1 (by rwa [he])
    rw [← output_error hl A _, he, length_factor hl] at hb
    exact hb
  · intro hzero
    obtain ⟨Y, hY, hopt⟩ := NLA.Proofs.TR04.exists_optimum S r A
    have hy := (input_feasible hl r Y).mp hY
    have he : error (m :: n :: ns) (input hl A) (input hl Y) = 0 := by
      rw [← input_error, ← hopt, hzero]
    have hx := (hcmp (input hl Y) hy).2 he
    rw [hx, output_input]

#assert_trust kernel output_minimum_iff
#assert_trust kernel first_svd_explicit_strict_family
#print axioms first_svd_explicit_strict_family
end NLA.Proofs.TR04.TensorFormat.TTStrict.Original
