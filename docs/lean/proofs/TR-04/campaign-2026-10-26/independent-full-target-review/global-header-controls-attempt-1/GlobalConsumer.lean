import GlobalOriginal
import LeanCert.Tactic.Verification

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

noncomputable section
#audit_named ".candidate_count_le_first_mode" "GlobalOriginal" "public" "theorem"
section

example
    {n₁ t k : Nat} (ht : t ≤ n₁) (hk : k ≤ t) : k ≤ n₁ := by
  exact @.candidate_count_le_first_mode n₁ t k ht hk
end
#audit_named ".cyclic_window_count_le_first_mode" "GlobalOriginal" "public" "theorem"
section

example
    {n₁ t : Nat} (ht : t ≤ n₁) : t ≤ n₁ := by
  exact @.cyclic_window_count_le_first_mode n₁ t ht
end
end
