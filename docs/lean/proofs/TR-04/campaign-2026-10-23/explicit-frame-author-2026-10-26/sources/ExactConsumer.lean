import NLA.Proofs.TR04.TTStrictExplicitFamily
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open NLA.Computation.SVDMachine NLA.Proofs.TR04.SVD
open NLA.Proofs.TR04.TensorFormat NLA.Proofs.TR04.TensorFormat.TTStrict
namespace ExplicitFrameExactConsumer

theorem literal_index {p h t : ℕ} [NeZero t] (ht : h + t ≤ p)
    (s : ℕ) (hst : s ≤ t) (j : Fin t) (k : Fin (h + s)) :
    (cyclicColumnIndex h t ht s hst j k).val =
      if k.val < h then k.val else h + ((j.val + (k.val - h)) % t) :=
  cyclicColumnIndex_val ht s hst j k
#assert_trust kernel literal_index

theorem literal_projector {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)} (T : TieStructure sigma a)
    (j : Fin T.tied) (B : Matrix (Fin m) (Fin l) ℝ) :
    Matrix.rank (T.explicitFrame U j) = a.val + 1 ∧
      T.explicitFrame U j * ((T.explicitFrame U j).transpose * B) =
        projectMatrix (directionSubspace U (tieSelection T.above T.tied T.fits T.take j)) B :=
  ⟨T.explicitFrame_rank hU j, T.explicitFrame_projection hU j B⟩
#assert_trust kernel literal_projector

theorem literal_family {m n : ℕ} {ns : List ℕ} {r : ℕ → ℕ}
    (hlen : 1 ≤ ns.length) (hr : 1 ≤ r 0) {A : Tensor (m :: n :: ns)}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m (suffixSize (n :: ns))) → ℝ}
    {V : Matrix (Fin (suffixSize (n :: ns))) (Fin (suffixSize (n :: ns))) ℝ}
    (h : ValidSVD (denseFirst A) U sigma V) :
    let F := explicitFirstFrames h (r 0)
    F.count ≤ min m (suffixSize (n :: ns)) + 1 ∧
      F.width ≤ min m (suffixSize (n :: ns)) ∧
      (∃ Z : Fin F.count → Tensor ((F.width * n) :: ns),
        ∀ j, Completion ((F.width * n) :: ns) (fun i => r (i + 1))
          (merge F.width n ns (contract (F.frame j) A)) (Z j)) ∧
      ∀ Z : Fin F.count → Tensor ((F.width * n) :: ns),
        (∀ j, Completion ((F.width * n) :: ns) (fun i => r (i + 1))
          (merge F.width n ns (contract (F.frame j) A)) (Z j)) →
        (∃ imin, IsMinimum A (fun j => completionOutput (F.frame j) (Z j)) imin) ∧
        ∀ imin, IsMinimum A (fun j => completionOutput (F.frame j) (Z j)) imin →
          RankFeasible (m :: n :: ns) r (completionOutput (F.frame imin) (Z imin)) ∧
          ∀ Y : Tensor (m :: n :: ns), RankFeasible (m :: n :: ns) r Y →
            (0 < error (m :: n :: ns) A Y →
              error (m :: n :: ns) A (completionOutput (F.frame imin) (Z imin)) <
                ((ns.length : ℝ) + 1) * error (m :: n :: ns) A Y) ∧
            (error (m :: n :: ns) A Y = 0 → completionOutput (F.frame imin) (Z imin) = A) :=
  explicit_strict_family hlen hr h
#assert_trust kernel literal_family
end ExplicitFrameExactConsumer
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicColumnIndex
#print axioms NLA.Proofs.TR04.SVD.cyclicColumnIndex
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicColumnIndex_val
#print axioms NLA.Proofs.TR04.SVD.cyclicColumnIndex_val
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicColumnIndex_injective
#print axioms NLA.Proofs.TR04.SVD.cyclicColumnIndex_injective
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicColumnIndex_mem
#print axioms NLA.Proofs.TR04.SVD.cyclicColumnIndex_mem
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicColumnIndex_surjective
#print axioms NLA.Proofs.TR04.SVD.cyclicColumnIndex_surjective
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicFrame
#print axioms NLA.Proofs.TR04.SVD.cyclicFrame
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicFrame_orthonormal
#print axioms NLA.Proofs.TR04.SVD.cyclicFrame_orthonormal
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicFrame_space
#print axioms NLA.Proofs.TR04.SVD.cyclicFrame_space
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicFrame_rank
#print axioms NLA.Proofs.TR04.SVD.cyclicFrame_rank
#assert_trust kernel NLA.Proofs.TR04.SVD.cyclicFrame_projection
#print axioms NLA.Proofs.TR04.SVD.cyclicFrame_projection
#assert_trust kernel NLA.Proofs.TR04.SVD.countedTieStructure
#print axioms NLA.Proofs.TR04.SVD.countedTieStructure
#assert_trust kernel NLA.Proofs.TR04.SVD.countedTieStructure_above
#print axioms NLA.Proofs.TR04.SVD.countedTieStructure_above
#assert_trust kernel NLA.Proofs.TR04.SVD.countedTieStructure_tied
#print axioms NLA.Proofs.TR04.SVD.countedTieStructure_tied
#assert_trust kernel NLA.Proofs.TR04.SVD.countedTieStructure_take
#print axioms NLA.Proofs.TR04.SVD.countedTieStructure_take
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitIndex
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitIndex
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_val
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_val
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_injective
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_injective
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_mem
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_mem
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_surjective
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitIndex_surjective
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitFrame
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitFrame
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_orthonormal
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_orthonormal
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_space
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_space
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_projection
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_projection
#assert_trust kernel NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_rank
#print axioms NLA.Proofs.TR04.SVD.TieStructure.explicitFrame_rank
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_eq_positive
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_eq_positive
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_eq_default_large
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_eq_default_large
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_eq_default_nonpos
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_eq_default_nonpos
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_width
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_width
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_column
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_column
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_count
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.positiveFrames_count
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_spec
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.explicitFirstFrames_spec
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.TTStrict.explicit_strict_family
#print axioms NLA.Proofs.TR04.TensorFormat.TTStrict.explicit_strict_family
