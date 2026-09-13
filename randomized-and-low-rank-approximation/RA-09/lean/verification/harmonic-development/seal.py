"""Seal the shared harmonic helper, initial author attempt and all later evidence."""
from pathlib import Path
import datetime,hashlib,json,re,shutil,subprocess
E=Path(__file__).resolve().parent;P=E.parents[1];W=P.parents[2]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
module=P/'NLA/RA09/Harmonic.lean'
assert sha(module)=='629f355ef949d3f11acbba443fe1ba8a77d7ac89fb10e76f223ef5a47e7be91e'
assert sha(P/'verification/proof-start.json')=='1838ba4734f82970700086ef9850cea848ffa7f72b52055e89b94d2a19678b8e'
assert sha(P/'verification/implementation-roles.json')=='6949645a1f5d5e139aa31014017df2990e23856ddfdd9377f7df520c7a5cf385'
assert sha(P/'verification/harmonic-ownership-transfer.json')=='bd051bd219b82a7f0576bf98c5d1c13d8edb19a20c3e566282322d4466159ba8'
f=json.loads((P/'reviews/statement-freeze.json').read_text())
for name,h in f['files'].items():assert sha(P/name)==h,name
for name,h in f['source_files'].items():
    raw=subprocess.check_output(['git','show',f['base']+':'+name],cwd=W)
    assert (W/name).read_bytes()==raw and sha(W/name)==h,name
initial=json.loads((E/'initial-handoff.json').read_text())
assert sha(E/'initial-Harmonic.lean.txt')==initial['source_sha256']
for name,h in initial['copied_files'].items():assert sha(E/'initial-author-attempt'/name)==h,name
scalar=P/'verification/scalar-development';sm=json.loads((scalar/'EVIDENCE-MANIFEST.json').read_text())
for name,row in sm['files'].items():assert sha(scalar/name)==row['sha256'],name
final=E/'final-97r28juw/result.json';r=json.loads(final.read_text())
assert r['result']=='PASS' and len(r['commands'])==4 and r['reachable_project_declarations']==5
for row in r['commands']:
    assert row['exit_code']==0 and sha(P/row['source'])==row['source_sha256']
    assert sha(final.parent/row['log'])==row['log_sha256']
source=re.sub(r'/\-[\s\S]*?\-/','',module.read_text());source=re.sub(r'--[^\n]*','',source)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|run_tac)\b',source)
assert 'import Challenge' not in source and 'import NLA.RA09.Spectral' not in source
prefix=Path(r['prefix']);assert prefix.name.startswith('ra09-harmonic-') and prefix.parent==Path('/tmp/nla-lean-formalization/independent-prefixes')
for row in r['fresh_object_hashes']:
    q=prefix/row['path'];assert sha(q)==row['sha256'] and q.stat().st_size==row['bytes']
shutil.rmtree(prefix)
cleanup={'scope':'Only owned disposable harmonic project prefix removed after final object hashes. Sources, evidence and shared MI22 dependencies preserved.',
 'path':str(prefix),'files':r['fresh_object_hashes'],'bytes':sum(x['bytes'] for x in r['fresh_object_hashes'])}
(E/'prefix-cleanup.json').write_text(json.dumps(cleanup,indent=2)+'\n')
handoff={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'initial_implementation_agent':'/root/leancert_examples','completion_agent':'/root/formal_review_standards',
 'both_independent_final_referee_eligible':False,'initial_source_sha256':initial['source_sha256'],
 'module':'NLA/RA09/Harmonic.lean','module_sha256':sha(module),'module_bytes':module.stat().st_size,
 'frozen_contract_export':'NLA.RA09.harmonic_constraint_proved',
 'auxiliary_exports':['NLA.RA09.outerSquare_mulVec','NLA.RA09.diagonal_outer_quadratic'],
 'exact_actual_frozen_type_matches':1,'kernel_standard_three_reports':6,
 'audited_reachable_project_declarations':5,'retained_material_dependencies':9,
 'fresh_local_commands':4,'proof_module_warnings':0,'intentional_Challenge_warnings':17,
 'final_result':'final-97r28juw/result.json','final_result_sha256':sha(final),
 'inspection_source_sha256':sha(E/'Inspect.lean'),'completion_sha256':sha(E/'completion.md'),
 'proof_gate_sha256':sha(P/'verification/proof-start.json'),
 'roles_sha256':sha(P/'verification/implementation-roles.json'),
 'ownership_transfer_sha256':sha(P/'verification/harmonic-ownership-transfer.json'),
 'statement_freeze_sha256':sha(P/'reviews/statement-freeze.json'),
 'preserved_statement_files':f['files'],'preserved_original_sources':f['source_files'],
 'preserved_original_Git_blobs':f['source_git_blobs'],'pins':r['pins'],
 'sealed_Scalar_evidence_files_preserved':len(sm['files']),
 'sealed_Scalar_outer_sha256':sha(scalar/'EVIDENCE-MANIFEST.json'),
 'scope':'Complete actual harmonic constraint helper only; full integration, independent final reviews and authoritative Linux verification pending.',
 'no_canonical_status_commit_or_push':True,'verdict':'READY FOR INTEGRATION'}
(E/'handoff.json').write_text(json.dumps(handoff,indent=2)+'\n')
outer=E/'EVIDENCE-MANIFEST.json'
files={str(p.relative_to(E)):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(E.rglob('*')) if p.is_file() and p!=outer}
files['../../NLA/RA09/Harmonic.lean']={'bytes':module.stat().st_size,'sha256':sha(module)}
outer.write_text(json.dumps({'scope':handoff['scope'],'files':files,'file_count':len(files),
 'self_exclusion':'Only this exact outer manifest path. All nested records and initial/later raw attempts retained.'},indent=2)+'\n')
for name,row in files.items():assert sha(E/name)==row['sha256'] and (E/name).stat().st_size==row['bytes']
print(json.dumps({'module_sha256':sha(module),'handoff_sha256':sha(E/'handoff.json'),
 'completion_sha256':sha(E/'completion.md'),'outer_sha256':sha(outer),
 'bound_files':len(files),'total_including_outer':len(files)+1,'disposable_prefix_removed':True},indent=2))
