import NLA.Proofs.TR04.TTStrictExplicitOriginal
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
open NLA.Computation.TensorTrainApproximation NLA.Computation.SVDMachine
open NLA.Proofs.TR04.TensorFormat NLA.Proofs.TR04.TensorFormat.TTStrict
open NLA.Proofs.TR04.TensorFormat.TTStrict.Original
namespace ExplicitOriginalExactConsumer

theorem literal_original_family (S : Shape) (r : Ranks S) (hr : ∀ j, 1 ≤ r j)
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
          (Optimum S r A = 0 → output hl (completionOutput (F.frame imin) (Z imin)) = A) :=
  first_svd_explicit_strict_family S r hr A hl h
#assert_trust kernel literal_original_family

theorem literal_sums_ranks_infimum (S : Shape) (r : Ranks S) (hr : ∀ j, 1 ≤ r j)
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
        (∃ imin, (∀ j, (∑ a : Index S, (A a - (output hl (completionOutput (F.frame imin) (Z imin))) a)^2) ≤
          (∑ a : Index S, (A a - (output hl (completionOutput (F.frame j) (Z j))) a)^2))) ∧
        ∀ imin, (∀ j, (∑ a : Index S, (A a - (output hl (completionOutput (F.frame imin) (Z imin))) a)^2) ≤
          (∑ a : Index S, (A a - (output hl (completionOutput (F.frame j) (Z j))) a)^2)) →
          (∀ j, Matrix.rank (Unfold S (output hl (completionOutput (F.frame imin) (Z imin))) j) ≤ r j) ∧
          (0 < (sInf {e : ℝ | ∃ Y : NLA.Computation.TensorTrainApproximation.Tensor S,
          (∀ j, Matrix.rank (Unfold S Y j) ≤ r j) ∧ e = ∑ a : Index S, (A a - Y a)^2}) →
            (∑ a : Index S, (A a - (output hl (completionOutput (F.frame imin) (Z imin))) a)^2) <
              ((S.order : ℝ) - 1) * (sInf {e : ℝ | ∃ Y : NLA.Computation.TensorTrainApproximation.Tensor S,
          (∀ j, Matrix.rank (Unfold S Y j) ≤ r j) ∧ e = ∑ a : Index S, (A a - Y a)^2})) ∧
          ((sInf {e : ℝ | ∃ Y : NLA.Computation.TensorTrainApproximation.Tensor S,
          (∀ j, Matrix.rank (Unfold S Y j) ≤ r j) ∧ e = ∑ a : Index S, (A a - Y a)^2}) = 0 → output hl (completionOutput (F.frame imin) (Z imin)) = A) := by
  simpa only [Optimum, Feasible, FrobeniusSq] using first_svd_explicit_strict_family S r hr A hl h
#assert_trust kernel literal_sums_ranks_infimum
end ExplicitOriginalExactConsumer
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.output_minimum_iff
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.Original.output_minimum_iff
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.first_svd_explicit_strict_family
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.Original.first_svd_explicit_strict_family
