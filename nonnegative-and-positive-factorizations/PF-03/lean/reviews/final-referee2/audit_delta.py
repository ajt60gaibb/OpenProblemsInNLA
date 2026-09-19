from pathlib import Path
import datetime,gzip,hashlib,json,re
import jsonschema
D=Path(__file__).resolve().parents[2]
O=Path(__file__).resolve().parent
P=D/'publication/PF03/nonnegative-and-positive-factorizations/PF-03/lean'
S=D/'development/PF03-agent-packaging-v1/project'
F=D/'publication/PF03-LOCAL-EVIDENCE-FREEZE.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
hashb=lambda b:hashlib.sha256(b).hexdigest()
assert sha(F)=='dc090fe6ccba8a12f344cb2392267a8f8ffad3be5cf1b552bb821e40fb0099d1'
f=json.loads(F.read_text())
assert all(sha(P/p)==h for p,h in f['files'].items())
sealed=json.loads((S.parent/'STAGING-HANDOFF.json').read_text())
lean_files=[p for p in sealed['project_files'] if p.endswith('.lean')]
assert all(sha(P/p)==sha(S/p) for p in lean_files)
for p in ['Challenge.lean','NUMERICAL_TARGETS.md','comparator.json','NLA/PF03/Definitions.lean','NLA/PF03/RawData.lean']:
 assert sha(P/p)==sha(S/p)
meta=json.loads((P/'formalization.yaml').read_text())
schema=json.loads((S.parent/'consulted/v0.4.schema.json').read_text())
jsonschema.validators.validator_for(schema)(schema).validate(meta)
assert meta['verification']['local_aggregate']['status']=='PASS'
assert meta['verification']['canonical_verification_completed'] is False
assert meta['verification']['GitHub_Comparator']['status']=='NOT_RUN_FOR_THIS_PACKAGE'
E=P/'verification/local-2026-09-19'
A=E/'LOCAL-REPLAY-AUDIT.json'
assert sha(A)=='1656823e9c87a11fb434c20d167cc0635a38014940078795fc22fb98eab62137'
a=json.loads(A.read_text());cached={}
for name,entry in a['lossless_original_receipts'].items():
 path=E/entry['file'];assert sha(path)==entry['gzip_sha256']
 raw=gzip.decompress(path.read_bytes());assert hashb(raw)==entry['original_sha256']
 obj=json.loads(raw);assert obj.get('end');cached[name]=(obj,hashb(raw))
assert len(cached)==30
assert cached['recovery-047'][1]==a['aggregate_receipt_sha256']
# Independently follow every archived reuse link back to an actual successful record.
outputs={r['module']:r['output_sha256'] for r in a['module_records']}
read_logs={};terminals={};visited_links=0
for r in a['module_records']:
 m=r['module'];assert sha(P/r['source'])==r['source_sha256']
 run='recovery-047';seen=set()
 initial=next(c for c in cached[run][0]['commands'] if c['module']==m)
 c=initial
 while c.get('status')=='reused_exact_successful_local_output':
  assert run not in seen;seen.add(run);visited_links+=1
  assert c['source_sha256']==r['source_sha256'] and c['output_sha256']==r['output_sha256']
  for src,h in c['transitive_source_hashes'].items(): assert sha(P/src)==h
  prior=Path(c['prior_receipt']).parent.name
  assert cached[prior][1]==c['prior_receipt_sha256']
  run=prior;c=next(x for x in cached[prior][0]['commands'] if x['module']==m)
 assert c['exit_code']==0 and c['source_sha256']==r['source_sha256'] and c['output_sha256']==r['output_sha256']
 assert run==r['fresh_success_run'] and c==r['actual_fresh_command']
 assert '--threads=1' in c['argv'] and '--memory=4096' in c['argv']
 for dep,h in c.get('dependency_olean_sha256',{}).items():assert outputs[dep]==h
 assert sha(E/r['log'])==c['log_sha256']
 olean=D/'local-lean/.lake/build/lib/lean'/(m.replace('.','/')+'.olean')
 assert sha(olean)==r['output_sha256']
 read_logs[m]={'log':r['log'],'sha256':sha(E/r['log'])}
 terminals[m]=run
assert len(terminals)==60
log=(E/'logs/recovery-047/Solution.log').read_text()
axioms={n:a.split(', ') for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)}
assert axioms==json.loads((E/'actual-axioms.json').read_text())
for result in meta['status']['main_results']:
 assert result['axioms']==axioms[result['declaration']] and result['sorry_count']==0
assert meta['verification']['local_aggregate']['receipt_sha256']==sha(A)
assert meta['verification']['local_aggregate']['log_sha256']==sha(E/'logs/recovery-047/Solution.log')
assert meta['verification']['local_aggregate']['source_sha256']==sha(P/'Solution.lean')
# Privacy scan of the changed metadata and all archived receipts.
pattern=r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}'
assert all(not re.search(pattern,(P/f).read_text()) for f in ['README.md','STATE.json','formalization.yaml'])
assert all(not re.search(pattern,json.dumps(r)) for r,_ in cached.values())
out={
 'reviewer':'/root/pf03_final_referee2','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'kind':'Independent read-only metadata and archived-receipt audit; no compiler or Comparator invocation',
 'delta_freeze_sha256':sha(F),'delta_files_checked':len(f['files']),
 'all_sealed_lean_bytes_unchanged':True,'sealed_lean_files':len(lean_files),
 'publication_metadata_hashes':{x:sha(P/x) for x in ['formalization.yaml','STATE.json','README.md']},
 'schema_validation':'PASS','local_replay_audit_sha256':sha(A),
 'lossless_original_receipts_checked':len(cached),'module_chains_checked':len(terminals),'reuse_links_checked':visited_links,
 'source_and_transitive_source_hash_checks':'PASS','recorded_dependency_olean_hash_checks':'PASS','current_olean_output_hash_checks':'PASS','archived_log_hash_checks':'PASS',
 'terminal_success_run_by_module':terminals,'actual_axiom_reports':axioms,
 'unchanged_canonical_completed_status':False,'GitHub_Comparator':'NOT_RUN_FOR_PF03',
 'Lean_rerun_by_this_reviewer':False,'standalone_lake_build':'NOT_RUN_BY_THIS_REVIEWER',
 'publication_privacy':'No email-pattern matches in updated metadata or 30 archived receipts',
 'limitations':'Hash consistency authenticates correspondence to the recorded local executions. It is not an independent compiler execution or an assurance against a malicious environment. GitHub Linux kernel/Comparator/sandbox checks remain required.',
 'count_change':0,
}
(O/'DELTA-AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['delta_files_checked','sealed_lean_files','schema_validation','lossless_original_receipts_checked','module_chains_checked','reuse_links_checked','GitHub_Comparator']},indent=2))
print('DELTA-AUDIT SHA',sha(O/'DELTA-AUDIT.json'))
