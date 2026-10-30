import NLA.Proofs.TR04.TTStrictOriginal
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.TR04.TensorFormat.TTStrict.Original.AuthorConsumer
open NLA.Computation.TensorTrainApproximation NLA.Computation.SVDMachine
theorem literal_all_responses (S : Shape) (r : Ranks S) (hr : ∀ j, 1 ≤ r j)
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
          (Optimum S r A = 0 → output hl (completionOutput (F.frame imin) (Z imin)) = A) :=
 first_svd_strict_family S r hr A hl h
theorem literal_original (S : Shape) (r : Ranks S) (hr : ∀ j, 1 ≤ r j)
 (A : NLA.Computation.TensorTrainApproximation.Tensor S) :
 ∃ X : NLA.Computation.TensorTrainApproximation.Tensor S, Feasible S r X ∧
 (0 < Optimum S r A → FrobeniusSq S A X < ((S.order : ℝ) - 1) * Optimum S r A) ∧
 (Optimum S r A = 0 → X = A) := exists_strict_tensor S r hr A
#assert_trust kernel literal_all_responses
#assert_trust kernel literal_original
#print axioms literal_all_responses
#print axioms literal_original
end NLA.Proofs.TR04.TensorFormat.TTStrict.Original.AuthorConsumer
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.error_eq_zero_iff
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.error_denseFirst
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.energy_projection_le
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.energy_projection_eq
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.error_projection_eq
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.completionOutput
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.IsMinimum
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.exists_minimum
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.completionOutput_bound
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.completionOutput_strict_of_first_lt
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.FirstFrames
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.defaultFrames
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.defaultFrames_first_error
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.exists_firstFrames
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.rank_denseFirst_le_first
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.family_first_error
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.family_projected_energy
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.family_completion_feasible
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.family_completion_bound
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.family_min_strict
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.family_completion_exact_of_error_zero
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.exists_strict_family
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.formatCast
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.formatCast_error
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.formatCast_feasible
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.input
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.output
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.input_output
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.output_input
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.input_error
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.output_error
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.input_feasible
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.output_feasible
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.first_rank_pos
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.exists_format
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.length_pos
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.length_factor
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.first_svd_strict_family
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.Original.exists_strict_tensor
