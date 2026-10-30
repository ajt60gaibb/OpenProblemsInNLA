#!/usr/bin/env python3
"""Read-only final promotion delta/preservation preflight; not a Linux receipt."""
import pathlib,json,hashlib,subprocess,ast,difflib,sys,importlib.util
sys.dont_write_bytecode=True
HERE=pathlib.Path(__file__).resolve().parent;REPO=HERE.parents[5];DOC=HERE.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();git=lambda *args:subprocess.check_output(['git',*args],cwd=REPO)
HEAD='09cd782576559502787fb536bc1427bf64b7b3e4';CANDIDATE='027aaefbadf602ac460d0cf4cae7beed3181d712';PROJECT='tensor-computations/TR-04/lean'
freeze=DOC/'CANONICAL_PROMOTION_FREEZE_2026-10-26.json';assert sha(freeze)=='44b5df77ea7ed70c35aac6e87b2001f2b6860a36f58f1156a50d01a3c83374f7';F=json.loads(freeze.read_text());inputs=F['inputs'];assert len(inputs)==205
assert hashlib.sha256(git('show',HEAD+':'+str(freeze.relative_to(REPO)))).hexdigest()==sha(freeze)
for q,h in inputs.items():assert sha(REPO/PROJECT/q)==h
actual={str(p.relative_to(REPO/PROJECT)) for p in (REPO/PROJECT).rglob('*') if p.is_file() and '.lake' not in p.relative_to(REPO/PROJECT).parts};assert actual==set(inputs)
old=json.loads((DOC/'CANONICAL_PACKAGE_PREACCEPTANCE_FREEZE_2026-10-26.json').read_text())['inputs'];assert set(old)==set(inputs) and [q for q in inputs if inputs[q]!=old[q]]==['formalization.yaml']
assert git('diff','--name-only',CANDIDATE,HEAD,'--',PROJECT,'tensor-computations/TR-04/README.md').decode().splitlines()==['tensor-computations/TR-04/README.md','tensor-computations/TR-04/lean/formalization.yaml']
assert sum(q.endswith('.lean') for q in inputs)==190 and all(inputs[q]==old[q] for q in inputs if q.endswith('.lean'))
proposal=DOC/'promotion-draft/PROMOTION_PROPOSAL.json';assert sha(proposal)=='c352fedca0c34cf23c89e41fdc82cb870ff552b5d50c6fe01a1fc6b5d47a11b0';P=json.loads(proposal.read_text());assert P['post_promotion_package_inputs']==inputs
for c in P['proposed_replacements']:assert sha(REPO/c['destination'])==c['proposed_sha256']==sha(REPO/c['proposed_path'])
for approval in F['promotion_approvals']:
 assert sha(REPO/approval['path'])==approval['sha256']
 claim=json.loads((REPO/approval['path']).read_text());assert claim['proposal_sha256']==sha(proposal)
 if approval['path'].endswith('/independent-promotion-review/APPROVAL.json'):assert claim['passed'] is True and claim['reviewer']=='/root/recover_verification'
 elif approval['path'].endswith('/independent-promotion-source-algebra/APPROVAL.json'):assert claim['outcome']=='approved' and claim['reviewer']=='/root/recover_algebra'
 else:raise AssertionError('Unexpected promotion reviewer')
archive=REPO/F['preserved_original_archive'];A=json.loads(archive.read_text());assert len(A['records'])==25
for c in A['records']:
 assert sha(REPO/c['archive_path'])==c['sha256']
 if c['original_path']!='tensor-computations/TR-04/README.md':assert sha(REPO/c['original_path'])==c['sha256']
new=(REPO/'tensor-computations/TR-04/README.md').read_bytes();before=git('show',CANDIDATE+':tensor-computations/TR-04/README.md');assert new.split(b'## Problem statement\n',1)[1]==before.split(b'## Problem statement\n',1)[1]
assert new.split(b'## Lean verification',1)[0].replace(b'**Status:** Lean verified',b'**Status:** Solved').replace(b'**Last checked:** 2026-10-26',b'**Last checked:** 2026-09-11')==before.split(b'## Lean formalization scaffold',1)[0]
assert len(json.loads((REPO/'problem_ids.json').read_text()))==217
lock=json.loads((REPO/PROJECT/'proof-source-lock.json').read_text());assert len(lock['copies'])==184 and lock['actual_proof_source_count']==179
for c in lock['copies']:assert sha(REPO/c['source'])==sha(REPO/c['destination'])==c['source_sha256']==c['destination_sha256']
for q in ['Challenge.lean','Solution.lean','SPEC.md','README.md','comparator.json','lakefile.toml','lake-manifest.json','lean-toolchain']:assert inputs[q]==old[q]
candidate=DOC/'independent-linux-candidate-algebra/audit-linux.py';current=HERE/'audit-linux.py';assert sha(candidate)=='82303ba91fbe0584d6ed4fb25890510fa31a13cb511330de5d69663b7cfabba2';assert sha(DOC/'independent-linux-candidate-algebra/terminal-result.json')=='576281c8bab2560176c60fdff3b4b4e5d638150092af15b1220213d55c0db6bf'
x,y=candidate.read_text(),current.read_text();oldtree,newtree=ast.parse(x),ast.parse(y)
for name in ['unique','decode','header','axiom_records','selected_exports','proof_consumer','probe_source']:
 oldfn=next(n for n in oldtree.body if isinstance(n,ast.FunctionDef) and n.name==name);newfn=next(n for n in newtree.body if isinstance(n,ast.FunctionDef) and n.name==name);assert ast.dump(oldfn)==ast.dump(newfn),name
start="  for marker in ['RETURN honest_with_inductives_and_quotients: accepted'";end="  check('all-provided-evidence-bytes-unchanged'";assert x[x.index(start):x.index(end)]==y[y.index(start):y.index(end)]
(HERE/'auditor-delta.diff').write_text(''.join(difflib.unified_diff(x.splitlines(True),y.splitlines(True),fromfile='accepted-candidate795/audit-linux.py',tofile='final-promotion/audit-linux.py')))
spec=importlib.util.spec_from_file_location('final_audit_preflight',current);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
legacy=(REPO/PROJECT/'logs/solution-mathlib-check-20260925.txt').read_text();assert m.axiom_records(legacy)==[(m.NAMES[0],[]),(m.NAMES[1],[])];assert m.axiom_records("'NLA.TR04.target' depends on axioms: [propext,\nClassical.choice, Quot.sound]")==[(m.NAMES[2],m.STANDARD)]
commands=[]
for cmd in [[sys.executable,'tools/lean/validate_manifest.py',PROJECT],[sys.executable,'docs/lean/proofs/TR-04/sync-canonical-proof.py'],[sys.executable,'tools/validate_problem_ids.py','--base-ref','origin/main']]:
 r=subprocess.run(cmd,cwd=REPO,text=True,capture_output=True);commands.append(dict(command=cmd,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr));assert r.returncode==0,commands[-1]
for q,h in inputs.items():assert sha(REPO/PROJECT/q)==h
result={'phase':'prepared-awaiting-final-original-Linux-evidence','passed':True,'actual_final_Linux_audit_run':False,'head':HEAD,'base':'01141f415715a27473cabc1f35ef898e86aafae2','expected_run':40408919808,'expected_job':121875088207,'fetched_merge_not_yet_execution_evidence':'5c58fa518732636edcb21c377f8014fa00f34480','PR':370,'final_freeze_sha256':sha(freeze),'proposed_and_applied_revision2_exact':True,'canonical_inputs':205,'package_delta_from_candidate':['formalization.yaml'],'Lean_inputs_unchanged':190,'shared_copies_unchanged':184,'proof_modules_unchanged':179,'original_archive_exact':25,'other_live_originals_exact':24,'original_README_math_suffix_exact':True,'IDs_unchanged':217,'legacy_canonical4_and_all_pins_exact':True,'candidate795_auditor_and_receipt_immutable':True,'all_pure_parsers_and_kernel_consumer_unchanged':True,'entire_rejection_isolation_pin_raw_command_guard_segment_unchanged':True,'candidate_auditor_sha256':sha(candidate),'final_auditor_sha256':sha(current),'auditor_delta_sha256':sha(HERE/'auditor-delta.diff'),'static_inspector_sha256':sha(pathlib.Path(__file__)),'commands':commands,'no_proof_package_status_mutation':True}
(HERE/'PREPARATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='commands'},indent=2))
