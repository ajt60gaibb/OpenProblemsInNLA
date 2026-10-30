import NLA.Proofs.TR04.TTStrictExplicitFrames

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04.TensorFormat.TTStrict
open NLA.Computation.SVDMachine

/-- The literal explicit family is fixed before all child responses. Every
actual child-completion family and every actual error minimum satisfy the
strict pointwise comparison and exact zero-error conclusion. -/
theorem explicit_strict_family {m n : ℕ} {ns : List ℕ} {r : ℕ → ℕ}
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
            (error (m :: n :: ns) A Y = 0 → completionOutput (F.frame imin) (Z imin) = A) := by
  classical
  dsimp only
  let F := explicitFirstFrames h (r 0)
  obtain ⟨hc, hw, hfirst, hgate⟩ := explicitFirstFrames_spec h (r 0) hr
  refine ⟨hc, hw, ?_, ?_⟩
  · choose Z hZ using fun j : Fin F.count => completion_exists ((F.width * n) :: ns)
      (fun i => r (i + 1)) (merge F.width n ns (contract (F.frame j) A))
    exact ⟨Z, hZ⟩
  · intro Z hZ
    refine ⟨exists_minimum A (fun j => completionOutput (F.frame j) (Z j)), ?_⟩
    intro imin hmin
    refine ⟨family_completion_feasible A F Z hZ imin, ?_⟩
    intro Y hY
    exact ⟨family_min_strict hlen h F hfirst hgate Z hZ imin hmin Y hY,
      fun hz => family_completion_exact_of_error_zero h F hfirst Z hZ Y hY hz imin⟩

#assert_trust kernel explicit_strict_family
#print axioms explicit_strict_family
end NLA.Proofs.TR04.TensorFormat.TTStrict
