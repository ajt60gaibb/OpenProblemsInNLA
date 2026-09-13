"""Seal once the independently audited MF-16 Linux candidate input inventory.
Every eligible project input is included; only the exact outer manifest excludes
itself. Generated objects/directories are explicitly documented noninputs.
No Lean, Lake, dependency, network, or Git mutation command is run.
"""
import datetime,json,os,subprocess
from pathlib import Path
from verify_inventory import E,P,W,OUTER,EXCLUDED_DIRS,EXCLUDED_SUFFIXES,eligible_files,sha,verify
assert not OUTER.exists(),'Refuse to overwrite an existing seal'
baseline=json.loads((E/'baseline.json').read_text())
assert baseline['input_count']==len(baseline['reviewer_entry_inputs'])==271
for name,item in baseline['reviewer_entry_inputs'].items():
    path=E/'formalization.initial.yaml' if name=='formalization.yaml' else P/name
    assert sha(path)==item['sha256'] and path.stat().st_size==item['bytes'],name
integrity=json.loads((E/'integrity.json').read_text())
assert integrity['result']=='PASS'
assert sha(P/'README.md')==integrity['current_README_sha256']
assert sha(P/'formalization.yaml')==integrity['current_formalization_yaml_sha256']
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=W).decode().strip()==baseline['base']
assert not subprocess.check_output(['git','diff','--name-only'],cwd=W)
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=W)
actual,observed=eligible_files()
# Check that no candidate input is silently omitted by Git ignore rules.
publication=subprocess.check_output(['git','ls-files','--cached','--others','--exclude-standard','-z','--',str(P.relative_to(W))],cwd=W).decode().split(chr(0))
assert {n for n in publication if n}=={str(path.relative_to(W)) for path in actual}
files={os.path.relpath(path,E):{'sha256':sha(path),'bytes':path.stat().st_size} for path in actual}
nested=sorted(name for name in files if Path(name).name==OUTER.name)
assert len(nested)==5
record={'phase':'MF-16 independently audited concrete Linux candidate; complete project input inventory',
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'local_date_America_New_York':'2026-09-12',
 'worktree':str(W),'project':str(P),'base':baseline['base'],
 'canonical_status':'Solved, unchanged; Linux verification pending',
 'wrapper_preparer':'/root, coordinator and disclosed route contributor',
 'independent_packaging_reviewer':'/root/mf16_final_referee, also prior independent final mathematical referee 1',
 'additional_mathematical_approvals_added':0,
 'path_base':'Directory containing this exact outer manifest',
 'inventory_scope':'Every actual project source, document and evidence input, including all nested manifests and retained reviewer failures',
 'exact_self_exclusion':str(OUTER.relative_to(P)),
 'generated_noninputs':{'directories':sorted(EXCLUDED_DIRS),'suffixes':sorted(EXCLUDED_SUFFIXES),'observed':observed},
 'file_count':len(files),'total_including_this_outer_manifest':len(files)+1,
 'nested_same_basename_manifests_included':nested,
 'wrapper_mutation_scope':['Root refreshed README and archived its exact frozen predecessor',
  'Root added formalization.yaml; independent reviewer made two approved note-spacing corrections with exact before/after archive and receipt'],
 'proof_freeze_sha256':sha(P/'verification/proof-freeze.json'),
 'statement_freeze_sha256':sha(P/'reviews/statement-freeze.json'),
 'handoff_sha256':sha(E/'CANDIDATE-HANDOFF.md'),'integrity_sha256':sha(E/'integrity.json'),
 'external_repository_context':'Fourteen original source files and unchanged verifier/schema/workflow/ID context are bound in frozen inventories and integrity.json against the stated published base',
 'Git_candidate_input_eligibility':'All eligible project inputs present in Git tracked-or-untracked publication inventory, with no ignored candidate omission',
 'actual_Linux_default_kernel_Comparator_controls':'pending','commit_push_publication':False,'files':files}
# Exclusive creation prevents accidental replacement of an earlier approval seal.
with OUTER.open('x') as stream:
    stream.write(json.dumps(record,indent=2)+'\n')
print(json.dumps(verify(),indent=2))
