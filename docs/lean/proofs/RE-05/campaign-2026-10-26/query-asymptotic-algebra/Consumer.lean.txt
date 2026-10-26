import NLA.Proofs.RE05.QueryAsymptotic
import Reviewed.RE05

set_option autoImplicit false
set_option leancert.trust "kernel"
open NLA.Computation.LinearFamilyQuery

open Lean Elab Command in
elab "#assert_theorem " n:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let some (.thmInfo _) := (← getEnv).find? decl |
    throwErrorAt n "constant is not an actual theorem"
  logInfo m!"AUDITED_THEOREM {decl}"

example : NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl

example (q : ℕ) (ε : ℝ) (hpos : 0 < ε) (hsmall : ε < 1 / 2) :
    15 * (2 * Real.sqrt ((q + 1 : ℕ) * baseWidth q (squaredAccuracy ε)) +
      8 * Real.log (20 * (q + 1 : ℕ)) + 1) ≤
    1000000 * Real.sqrt (q + 1 : ℕ) * ε⁻¹ *
      (1 + Real.log (2 + (q + 1 : ℕ)) + Real.log (1 / ε)) :=
  NLA.Proofs.RE05.sourceQueryBound_numeric q ε hpos hsmall

example (n q : ℕ) (P : Basis n q) (ε : ℝ)
    (hpos : 0 < ε) (hsmall : ε < 1 / 2)
    (hsource : ∀ ω : ℕ → ℝ,
      ((batchQueries (plans P ε ω)).length : ℝ) ≤
        15 * (2 * Real.sqrt ((q + 1 : ℕ) * baseWidth q (squaredAccuracy ε)) +
          8 * Real.log (20 * (q + 1 : ℕ)) + 1)) :
    ∀ ω : ℕ → ℝ,
      ((batchQueries (plans P ε ω)).length : ℝ) ≤
        1000000 * Real.sqrt (q + 1 : ℕ) * (ε⁻¹) ^ 1 *
          (1 + Real.log (2 + (q + 1 : ℕ)) + Real.log (1 / ε)) ^ 1 :=
  NLA.Proofs.RE05.queryBound_of_sourceQueryBound P ε hpos hsmall hsource

example : ∃ C : ℝ, 0 < C ∧ ∃ a b : ℕ,
    ∀ (n q : ℕ) (P : Basis n q) (ε : ℝ), 0 < ε → ε < 1 / 2 →
      NLA.Statements.RE05.SourceQueryBound P ε →
        NLA.Statements.RE05.QueryBound P ε C a b := by
  refine ⟨1000000, by norm_num, 1, 1, ?_⟩
  exact fun _ _ P ε hp hs hsource =>
    NLA.Proofs.RE05.queryBound_of_sourceQueryBound P ε hp hs hsource

#assert_theorem NLA.Proofs.RE05.sourceQueryBound_numeric
#assert_trust kernel NLA.Proofs.RE05.sourceQueryBound_numeric
#print axioms NLA.Proofs.RE05.sourceQueryBound_numeric
#assert_theorem NLA.Proofs.RE05.queryBound_of_sourceQueryBound
#assert_trust kernel NLA.Proofs.RE05.queryBound_of_sourceQueryBound
#print axioms NLA.Proofs.RE05.queryBound_of_sourceQueryBound
