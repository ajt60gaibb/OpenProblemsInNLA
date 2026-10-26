#!/usr/bin/env python3
"""Derive the independent driver with exact public/private/local constant checks."""
from pathlib import Path
BASE = Path(__file__).resolve().parent
PRIOR = BASE.parent / "independent-dimension-review"
s = (PRIOR / "replay.py").read_text()


def replace(old, new):
    global s
    assert s.count(old) == 1, old[:100]
    s = s.replace(old, new)


replace("assert all(d['visibility']=='public' for d in all_declarations),'Private/local declaration requires explicit resolver'",
    "assert all(d['visibility'] in {'public','private','local'} for d in all_declarations)\nfor d in all_declarations:\n if d['visibility']=='private':\n  p=config['private_name_map'][d['name']];assert p['source']==d['source'] and p['line']==d['line'] and p['kind']==d['kind']\nassert sha((BASE/'private-name-provenance.json').read_bytes())==config['private_name_provenance_sha256']")
a = s.index("preamble='''")
b = s.index("consumers={}", a)
s = s[:a] + '''preamble=\'\'\'
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
  logInfo m!"AUDITED_KIND {user.getString} {expected.getString}"
  logInfo m!"AUDITED_ACTUAL {user.getString} {decl.toString} {visibility.getString}"
  elabCommand (← `(#assert_trust kernel $(mkIdent decl)))
  elabCommand (← `(#print axioms $(mkIdent decl)))
  let axs ← liftCoreM <| collectAxioms decl
  let body := String.intercalate "," (axs.toList.map Name.toString)
  logInfo m!"AUDITED_AXIOMS {user.getString} [{body}]"
\'\'\'
''' + s[b:]
replace("'NLA.Proofs.TR04.bestCandidateProgram_nonzero_realRegisters'}",
    "'NLA.Proofs.TR04.bestCandidateProgram_nonzero_realRegisters','NLA.Proofs.TR04.ttStartup_nonzero_realRegisters','NLA.Proofs.TR04.ttMetadata_nonzero_realRegisters','NLA.Proofs.TR04.ttFirstSelection_nonzero_reals'}")
replace("text+=f'#assert_kind {d[\"name\"]} \"{kind}\"\\n#assert_trust kernel {d[\"name\"]}\\n#print axioms {d[\"name\"]}\\n'",
    "module=d['source'].removesuffix('.lean').replace('/','.')\n  text+=f'#audit_named {json.dumps(d[\"name\"])} {json.dumps(module)} {json.dumps(d[\"visibility\"])} {json.dumps(kind)}\\n'")
replace("'private_or_local_named_declarations':[],'lean_version'",
    "'private_or_local_named_declarations':[d for d in all_declarations if d['visibility']!='public'],'private_name_provenance_sha256':config['private_name_provenance_sha256'],'lean_version'")
old = ''' axiom_records=re.findall(r"'([^']+)' depends on axioms:\\s*\\[([^\\]]*)\\]",log);no_axioms=re.findall(r"'([^']+)' does not depend on any axioms",log)
 observed=sorted({a.strip() for _,body in axiom_records for a in body.split(',') if a.strip()})
 names=[n for n,_ in axiom_records]+no_axioms;expected_names=[d['name'] for d in b['declarations']]'''
new = ''' axiom_records=re.findall(r'AUDITED_AXIOMS (\\S+) \\[([^\\]]*)\\]',log)
 observed=sorted({a.strip() for _,body in axiom_records for a in body.split(',') if a.strip()})
 names=[n for n,_ in axiom_records];expected_names=[d['name'] for d in b['declarations']]
 actual_bindings=re.findall(r'AUDITED_ACTUAL (\\S+) (\\S+) (\\S+)',log)
 expected_bindings=[(d['name'],config['private_name_map'][d['name']]['actual_kernel_name'] if d['visibility']=='private' else d['name'],d['visibility']) for d in b['declarations']]
 bindings_passed=sorted(actual_bindings)==sorted(expected_bindings)'''
replace(old, new)
replace("'all_named_declaration_checks_passed':sorted(names)==sorted(expected_names) and sorted(n for n,_ in kinds)==sorted(expected_names)",
    "'all_named_declaration_checks_passed':sorted(names)==sorted(expected_names) and sorted(n for n,_ in kinds)==sorted(expected_names) and bindings_passed,'actual_name_bindings':[{'source_name':n,'actual_kernel_name':a,'visibility':v} for n,a,v in actual_bindings],'actual_name_bindings_passed':bindings_passed")
replace("'private_or_local_named_declarations':[]}",
    "'private_or_local_named_declarations':[d for d in b['declarations'] if d['visibility']!='public'],'author_selected_public_declarations':b['author_selected_public_declarations']}")
(BASE / "replay.py").write_text(s)
print("Created exact private/public/local audit driver; no frozen proof or trust policy edits.")
