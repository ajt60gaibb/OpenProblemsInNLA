import Lean

/-! A statement is a closed, safe proposition definition, not a proof of that
proposition. This command checks its elaborated declaration and complete axiom
closure. Independent review must still establish its informal meaning. -/

open Lean Elab Command

elab "#assert_statement " target:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  liftCoreM do
    let info ← getConstInfo name
    let .defnInfo definition := info
      | throwError "statement target must be a definition"
    unless definition.safety == .safe do
      throwError "statement target must be safe"
    unless definition.type == mkSort .zero do
      throwError "statement target must have the closed type Prop"
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless axiomName == ``propext || axiomName == ``Classical.choice ||
          axiomName == ``Quot.sound do
        throwError "statement target has a forbidden axiom: {axiomName}"
