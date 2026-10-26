import NLA.Proofs.TR04.TTStrictOriginalView

/-! The strict mathematical construction at the immutable original tensor,
rank, squared-error and actual sInf optimum boundary. The finite RAM program
and its operation count are separate obligations. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04.TensorFormat.TTStrict.Original
open NLA.Computation.TensorTrainApproximation NLA.Computation.SVDMachine

/-- Every supplied legal first SVD admits a comparator-independent finite
frame family. Every actual choice of its legal child completions, and every
minimum of their actual original Frobenius errors, satisfies the strict
pointwise factor and exact zero-optimum recovery. -/
theorem first_svd_strict_family (S : Shape) (r : Ranks S) (hr : ∀ j, 1 ≤ r j)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S)
    {m n : ℕ} {ns : List ℕ} (hl : modeList S.mode = m :: n :: ns)
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m (suffixSize (n :: ns))) → ℝ}
    {V : Matrix (Fin (suffixSize (n :: ns))) (Fin (suffixSize (n :: ns))) ℝ}
    (h : ValidSVD (denseFirst (input hl A)) U sigma V) :
    ∃ F : FirstFrames m (originalRanks S r 0),
      F.count ≤ min m (suffixSize (n :: ns)) + 1 ∧ F.width ≤ min m (suffixSize (n :: ns)) ∧
      (∃ Z : Fin F.count → TensorFormat.Tensor ((F.width * n) :: ns),
        ∀ j, Completion ((F.width * n) :: ns) (fun i => originalRanks S r (i + 1))
          (merge F.width n ns (contract (F.frame j) (input hl A))) (Z j)) ∧
      ∀ Z : Fin F.count → TensorFormat.Tensor ((F.width * n) :: ns),
        (∀ j, Completion ((F.width * n) :: ns) (fun i => originalRanks S r (i + 1))
          (merge F.width n ns (contract (F.frame j) (input hl A))) (Z j)) →
        (∃ imin, IsMinimum (input hl A) (fun j => completionOutput (F.frame j) (Z j)) imin) ∧
        ∀ imin, IsMinimum (input hl A) (fun j => completionOutput (F.frame j) (Z j)) imin →
          Feasible S r (output hl (completionOutput (F.frame imin) (Z imin))) ∧
          (0 < Optimum S r A →
            FrobeniusSq S A (output hl (completionOutput (F.frame imin) (Z imin))) <
              ((S.order : ℝ) - 1) * Optimum S r A) ∧
          (Optimum S r A = 0 → output hl (completionOutput (F.frame imin) (Z imin)) = A) := by
  obtain ⟨F, hc, hw, hex, hall⟩ := exists_strict_family (length_pos hl) (first_rank_pos S r hr) h
  refine ⟨F, hc, hw, hex, ?_⟩
  intro Z hZ
  obtain ⟨hminex, hminall⟩ := hall Z hZ
  refine ⟨hminex, ?_⟩
  intro imin hmin
  obtain ⟨hfeas, hcmp⟩ := hminall imin hmin
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

/-- The original mathematical approximation guarantee, obtained by an actual
minimum of finitely many actual completed candidate tensors. This theorem
does not by itself supply the required finite arithmetic RAM implementation. -/
theorem exists_strict_tensor (S : Shape) (r : Ranks S) (hr : ∀ j, 1 ≤ r j)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S) :
    ∃ X : NLA.Computation.TensorTrainApproximation.Tensor S, Feasible S r X ∧
      (0 < Optimum S r A → FrobeniusSq S A X < ((S.order : ℝ) - 1) * Optimum S r A) ∧
      (Optimum S r A = 0 → X = A) := by
  classical
  obtain ⟨m, n, ns, hl, _⟩ := exists_format S
  obtain ⟨U, sigma, V, hSVD⟩ := SVD.exists_validSVD (denseFirst (input hl A))
  obtain ⟨F, _, _, ⟨Z, hZ⟩, hall⟩ := first_svd_strict_family S r hr A hl hSVD
  obtain ⟨⟨imin, hmin⟩, hprop⟩ := hall Z hZ
  exact ⟨output hl (completionOutput (F.frame imin) (Z imin)), hprop imin hmin⟩

#assert_trust kernel first_svd_strict_family
#assert_trust kernel exists_strict_tensor
#print axioms first_svd_strict_family
#print axioms exists_strict_tensor
end NLA.Proofs.TR04.TensorFormat.TTStrict.Original
