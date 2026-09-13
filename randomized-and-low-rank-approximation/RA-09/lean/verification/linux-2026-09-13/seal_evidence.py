"""Seal once all actual RA-09 operational evidence; preserve original candidate."""
import datetime,json,re
from pathlib import Path
from verify_inventory import O,C,OUTER,sha,files,candidate,verify
assert not OUTER.exists(),'Refuse to overwrite an existing evidence seal'
assert candidate(True)==524
runtime=json.loads((O/'runtime-verification.json').read_text())
assert runtime['result']=='PASS independent actual Ubuntu operational checks'
assert runtime['default_kernel_replay']==runtime['statement_comparator']=='accepted'
assert runtime['whole_workflow_jobs']==17 and runtime['actual_standard_three_axiom_reports']==49
assert runtime['candidate_source_inputs_matched_to_actual_receipt']==524
attempts=[];failures=[]
for f in sorted((O/'review-attempts').glob('*/result.json')):
    r=json.loads(f.read_text())
    if r['exit_code']!=0:
        assert f.parent.name=='20260913T050216.848070Z-source_audit' and r['exit_code']==1
        assert 'TypeError: string indices must be integers' in (f.parent/'raw.log').read_text()
        assert r['script_sha256']==sha(O/'corrections/root-prior-format/source_audit.py.before.txt')
        failures.append(str(f.relative_to(O)))
    assert sha(f.parent/'raw.log')==r['raw_log_sha256']
    assert sha(f.parent/r['source_snapshot'])==r['script_sha256']
    if r['exit_code']==0:attempts.append(str(f.relative_to(O)))
assert len(attempts)==6 and len(failures)==1
for p in files():
    try:t=p.read_text()
    except UnicodeDecodeError:continue
    for m in re.finditer(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',t):
        assert not any(x in m.group(0).lower() for x in ['stepaniants','george']),(p,'George email')
bound={str(p.relative_to(O)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in files()}
record={'result':'PASS independent actual Ubuntu operational review; coordinator acceptance and publication remain separate',
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'run':C['run'],'permanent_ID_run':C['permanent_id_run'],
 'candidate_commit':C['commit'],'project':C['project'],'reviewer':C['reviewer'],'reviewer_role':C['role'],
 'original_candidate_inputs_preserved':524,'actual_exports':17,'actual_standard_three_axiom_reports':49,
 'file_count':len(bound),'total_including_outer':len(bound)+1,'exact_self_exclusion':'EVIDENCE-MANIFEST.json',
 'inventory_scope':'Every actual operational evidence file recursively, including every nested same-basename manifest in the complete retained original candidate snapshot. Only this exact outer file is excluded.',
 'nested_same_basename_manifests_included':sum(Path(n).name=='EVIDENCE-MANIFEST.json' for n in bound),
 'operational_review_sha256':sha(O/'OPERATIONAL-REVIEW.md'),'runtime_verification_sha256':sha(O/'runtime-verification.json'),
 'successful_raw_audit_receipts':attempts,'preserved_failed_reviewer_receipts':failures,'George_email_matches':0,'files':bound}
with OUTER.open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
print(json.dumps(verify(True),indent=2))
