"""Seal the complete scalar helper and all raw development evidence."""
from pathlib import Path
import datetime,hashlib,json,re,shutil,subprocess
E=Path(__file__).resolve().parent;P=E.parents[1];W=P.parents[2]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
module=P/'NLA/RA09/Scalar.lean'
assert sha(module)=='be27edbd0f42e83fb825095bae65c48c8d90e8d1614ed90871abace1f55b6f17'
assert sha(P/'verification/proof-start.json')=='1838ba4734f82970700086ef9850cea848ffa7f72b52055e89b94d2a19678b8e'
assert sha(P/'verification/implementation-roles.json')=='6949645a1f5d5e139aa31014017df2990e23856ddfdd9377f7df520c7a5cf385'
f=json.loads((P/'reviews/statement-freeze.json').read_text())
for name,h in f['files'].items():assert sha(P/name)==h,name
for name,h in f['source_files'].items():
    raw=subprocess.check_output(['git','show',f['base']+':'+name],cwd=W)
    assert (W/name).read_bytes()==raw and sha(W/name)==h,name
final=E/'final-4qsv7b4x/result.json';r=json.loads(final.read_text())
assert r['result']=='PASS' and len(r['commands'])==4 and r['reachable_project_declarations']==10
for row in r['commands']:
    assert row['exit_code']==0 and sha(P/row['source'])==row['source_sha256']
    assert sha(final.parent/row['log'])==row['log_sha256']
source=re.sub(r'/\-[\s\S]*?\-/','',module.read_text());source=re.sub(r'--[^\n]*','',source)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|run_tac)\b',source)
assert 'import Challenge' not in source
prefix=Path(r['prefix']);assert prefix.name.startswith('ra09-scalar-') and prefix.parent==Path('/tmp/nla-lean-formalization/independent-prefixes')
for row in r['fresh_object_hashes']:
    q=prefix/row['path'];assert sha(q)==row['sha256'] and q.stat().st_size==row['bytes']
shutil.rmtree(prefix)
cleanup={'scope':'Removed only owned disposable scalar project prefix after final object hash checks; sources, evidence and all MI22 dependencies preserved.',
 'path':str(prefix),'files':r['fresh_object_hashes'],'bytes':sum(x['bytes'] for x in r['fresh_object_hashes'])}
(E/'prefix-cleanup.json').write_text(json.dumps(cleanup,indent=2)+'\n')
handoff={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'authoring_agent':'/root/formal_review_standards','independent_final_referee_eligible':False,
 'module':'NLA/RA09/Scalar.lean','module_sha256':sha(module),'module_bytes':module.stat().st_size,
 'exports':['NLA.RA09.admissible_scalar_consequences_proved','NLA.RA09.scalar_branch_certificates_proved','NLA.RA09.ordered_scalar_certificate_proved'],
 'exact_frozen_actual_type_matches':3,'kernel_standard_three_reports':8,'audited_reachable_project_declarations':10,
 'substantive_scalar_declarations_kernel_audited':5,'retained_named_semantic_dependencies':7,'retained_private_proof_helpers':2,
 'fresh_local_commands':4,'proof_module_warnings':0,'intentional_Challenge_warnings':17,
 'final_result':'final-4qsv7b4x/result.json','final_result_sha256':sha(final),
 'inspection_source_sha256':sha(E/'Inspect.lean'),'completion_sha256':sha(E/'completion.md'),
 'proof_gate_sha256':sha(P/'verification/proof-start.json'),'roles_sha256':sha(P/'verification/implementation-roles.json'),
 'statement_freeze_sha256':sha(P/'reviews/statement-freeze.json'),
 'preserved_statement_files':f['files'],'preserved_original_sources':f['source_files'],
 'preserved_original_Git_blobs':f['source_git_blobs'],'pins':r['pins'],
 'scope':'Complete exact scalar helper only; full project integration, two independent final reviews and authoritative Linux verification pending.',
 'no_canonical_status_commit_or_push':True,'verdict':'READY FOR INTEGRATION'}
(E/'handoff.json').write_text(json.dumps(handoff,indent=2)+'\n')
outer=E/'EVIDENCE-MANIFEST.json'
files={str(p.relative_to(E)):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(E.rglob('*')) if p.is_file() and p!=outer}
files['../../NLA/RA09/Scalar.lean']={'bytes':module.stat().st_size,'sha256':sha(module)}
outer.write_text(json.dumps({'scope':handoff['scope'],'files':files,'file_count':len(files),
 'self_exclusion':'Only this exact outer manifest path. Every nested manifest and raw attempt is retained.'},indent=2)+'\n')
for name,row in files.items():assert sha(E/name)==row['sha256'] and (E/name).stat().st_size==row['bytes']
print(json.dumps({'module_sha256':sha(module),'handoff_sha256':sha(E/'handoff.json'),
 'completion_sha256':sha(E/'completion.md'),'outer_sha256':sha(outer),
 'bound_files':len(files),'total_including_outer':len(files)+1,'disposable_prefix_removed':True},indent=2))
