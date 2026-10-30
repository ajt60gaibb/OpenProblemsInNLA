#!/usr/bin/env python3
"""Read-only frozen canonical inventory/type/import/schema/ID inspection; no Lean build."""
import hashlib,json,pathlib,re,subprocess,sys
HERE=pathlib.Path(__file__).resolve().parent;REPO=HERE.parents[5]
PROJECT=REPO/'tensor-computations/TR-04/lean';DOCS=HERE.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
freeze_path=DOCS/'CANONICAL_PACKAGE_PREACCEPTANCE_FREEZE_2026-10-26.json'
assert sha(freeze_path)=='8ee1d4585f3c0a60b101ec962fa9631ebbc043270cf35360669b8018152301eb'
freeze=json.loads(freeze_path.read_text());inputs=freeze['inputs'];assert len(inputs)==205

def check_inventory():
 for rel,digest in inputs.items():assert sha(PROJECT/rel)==digest,rel
 actual={str(p.relative_to(PROJECT)) for p in PROJECT.rglob('*') if p.is_file() and '.lake' not in p.relative_to(PROJECT).parts}
 assert actual==set(inputs),{'extra':sorted(actual-set(inputs)),'missing':sorted(set(inputs)-actual)}
check_inventory()
lock=json.loads((PROJECT/'proof-source-lock.json').read_text());assert len(lock['copies'])==184
for c in lock['copies']:
 assert sha(REPO/c['source'])==c['source_sha256']==c['destination_sha256']==sha(REPO/c['destination']),c['module']
assert len([p for p in inputs if p.endswith('.lean')])==190
assert sum(c['module'].startswith('NLA.Proofs.TR04.') for c in lock['copies'])==179
archive=REPO/freeze['original_archive']['path'];assert sha(archive)==freeze['original_archive']['sha256']
originals=json.loads(archive.read_text())['records'];assert len(originals)==25
for c in originals:assert sha(REPO/c['original_path'])==sha(REPO/c['archive_path'])==c['sha256'],c['original_path']
pins=lambda j:{x['name']:(x['url'],x['rev']) for x in j['packages']}
original_manifest=json.loads((REPO/'lean-statements/lake-manifest.json').read_text())
canonical_manifest=json.loads((PROJECT/'lake-manifest.json').read_text())
assert pins(original_manifest)==pins(canonical_manifest);assert len(pins(canonical_manifest))==10
for name,(url,rev) in pins(canonical_manifest).items():assert re.fullmatch('[0-9a-f]{40}',rev),name
assert (PROJECT/'lean-toolchain').read_bytes()==(REPO/'lean-statements/lean-toolchain').read_bytes()
registry=json.loads((REPO/'problem_ids.json').read_text());assert len(registry)==217
seen=set();pending=['FullSolution']
while pending:
 n=pending.pop()
 if n in seen:continue
 seen.add(n);p=PROJECT/pathlib.Path(n.replace('.','/')+'.lean')
 if not p.exists():continue
 for line in re.findall(r'^import\s+(.+)$',p.read_text(),re.M):pending+=line.split('--')[0].split()
assert not ({'Challenge','FullChallenge'}&seen)
def header(txt,name):
 a=txt.index('theorem '+name);z=txt.index(':=',a);return ' '.join(txt[a:z].split())
challenge=(PROJECT/'Challenge.lean').read_text();solution=(PROJECT/'Solution.lean').read_text()
for name in ['candidate_count_le_first_mode','cyclic_window_count_le_first_mode']:assert header(challenge,name)==header(solution,name)
assert header((PROJECT/'FullChallenge.lean').read_text(),'target')==header((PROJECT/'FullSolution.lean').read_text(),'target')=='theorem target : NLA.Statements.TR04.Target'
body=lambda t:t.split('def Target : Prop :=',1)[1].split('#assert_statement',1)[0]
assert body((PROJECT/'NLA/Statements/TR04.lean').read_text())==body((PROJECT/'Reviewed/TR04.lean').read_text())
config=json.loads((PROJECT/'comparator.json').read_text());assert config['theorem_names']==freeze['selected_exports'];assert config['definition_names']==[]
assert config['challenge_module']=='FullChallenge' and config['solution_module']=='FullSolution'
assert set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert 'NLA.Statements.TR04.Target=NLA.ReviewedStatements.TR04.Target := rfl' in (PROJECT/'Identity.lean').read_text()
assert not re.search(r'^\s*(axiom|unsafe)\b',(PROJECT/'FullSolution.lean').read_text(),re.M)
commands=[]
for cmd in [[sys.executable,'docs/lean/proofs/TR-04/sync-canonical-proof.py'],[str(REPO.parent/'tooling/metadata-venv/bin/python'),'tools/lean/validate_manifest.py','tensor-computations/TR-04/lean'],[sys.executable,'tools/validate_problem_ids.py','--base-ref','origin/main']]:
 r=subprocess.run(cmd,cwd=REPO,text=True,capture_output=True);commands.append({'command':cmd,'exit_code':r.returncode,'stdout':r.stdout,'stderr':r.stderr});assert r.returncode==0,commands[-1]
check_inventory()
result={'reviewer':'/root/recover_algebra','kind':'source/inventory/schema review; no Lean replay','success':True,'package_inputs':205,'Lean_inputs':190,'exact_shared_copies':184,'proof_modules':179,'selected_exports':config['theorem_names'],'no_definition_holes':True,'dependency_pins':pins(canonical_manifest),'live_and_archive_originals':25,'permanent_problem_IDs':217,'solution_import_separation':True,'literal_three_theorem_headers_match':True,'literal_target_reviewed_body_match':True,'identity_is_rfl':True,'package_hashes_before_and_after_exact':True,'freeze_sha256':sha(freeze_path),'proof_source_lock_sha256':sha(PROJECT/'proof-source-lock.json'),'original_archive_manifest_sha256':sha(archive),'inspector_sha256':sha(pathlib.Path(__file__)),'commands':commands,'tool_inputs':{p:sha(REPO/p) for p in ['docs/lean/proofs/TR-04/sync-canonical-proof.py','tools/lean/validate_manifest.py','docs/lean/schema/v0.4.schema.json','tools/validate_problem_ids.py']},'independent_proof_replay':False,'Linux_CI_claim':False,'Comparator_execution_claim':False,'own_authored_proof_prerequisites_excluded_from_independent_mathematical_scope':True}
(HERE/'inventory-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['commands','dependency_pins','tool_inputs']},indent=2))
