import NLA.Proofs.RE05.SelectedCharge
import NLA.Proofs.RE05.QueryAsymptotic
import Reviewed.RE05

set_option autoImplicit false
set_option leancert.trust "kernel"
open Lean Elab Command in
elab "#audit_named " user:str modName:str visibility:str expected:str : command => do
  unless visibility.getString == "public" || visibility.getString == "private" || visibility.getString == "local" do
    throwErrorAt visibility "unsupported visibility"
  let decl := if visibility.getString == "private" then
    Lean.mkPrivateNameCore modName.getString.toName user.getString.toName
    else user.getString.toName
  let some info := (← getEnv).find? decl | throwErrorAt user "missing exact compiler constant {decl}"
  match expected.getString, info with
  | "theorem", .thmInfo _ => pure ()
  | "definition", .defnInfo _ => pure ()
  | "inductive", .inductInfo _ => pure ()
  | _, _ => throwErrorAt user "constant kind differs from frozen source"
  logInfo m!"AUDITED_KIND {decl.toString} {expected.getString}"
  logInfo m!"AUDITED_ACTUAL {user.getString} {decl.toString} {visibility.getString}"
  elabCommand (← `(#assert_trust $(mkIdent `kernel) $(mkIdent decl)))
  elabCommand (← `(#print axioms $(mkIdent decl)))
  let axs ← liftCoreM <| collectAxioms decl
  let body := String.intercalate "," (axs.toList.map Name.toString)
  logInfo m!"AUDITED_AXIOMS {decl.toString} [{body}]"

namespace RE05IndependentComposition
open NLA.Computation.LinearFamilyQuery

theorem actual_query_cap {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (ε : ℝ) (hpos : 0 < ε) (hsmall : ε < 1 / 2) :
    ∀ ω : ℕ → ℝ, ((batchQueries (plans P ε ω)).length : ℝ) ≤
      1000000 * Real.sqrt (q + 1 : ℕ) * ε⁻¹ *
        (1 + Real.log (2 + (q + 1 : ℕ)) + Real.log (1 / ε)) := by
  simpa only [NLA.Statements.RE05.QueryBound, pow_one] using
    NLA.Proofs.RE05.queryBound_of_sourceQueryBound P ε hpos hsmall
      (NLA.Proofs.RE05.sourceQueryBound P hP ε hpos)

theorem uniform_deterministic_constants : ∃ C : ℝ, 0 < C ∧ ∃ a b : ℕ,
    ∀ (n q : ℕ), 0 < n → q + 1 ≤ n * n →
      ∀ P : Basis n q, Independent P →
        ∀ A : Square n, ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
          NLA.Statements.RE05.QueryBound P ε C a b := by
  refine ⟨1000000, by norm_num, 1, 1, ?_⟩
  intro n q _hn _hqn P hP _A ε hpos hsmall
  exact NLA.Proofs.RE05.queryBound_of_sourceQueryBound P ε hpos hsmall
    (NLA.Proofs.RE05.sourceQueryBound P hP ε hpos)

theorem reviewed_Target_identity :
    NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl

#audit_named "RE05IndependentComposition.actual_query_cap" "IndependentQueryComposition" "public" "theorem"
#audit_named "RE05IndependentComposition.uniform_deterministic_constants" "IndependentQueryComposition" "public" "theorem"
#audit_named "RE05IndependentComposition.reviewed_Target_identity" "IndependentQueryComposition" "public" "theorem"
end RE05IndependentComposition
