"""Independent read-only exact-parent, scope, and fingerprint audit for PR93/103."""
from pathlib import Path
import collections,hashlib,json,re,subprocess

OUT=Path(__file__).resolve().parent
REPO='/private/tmp/nla-pr83-delta-review'
INCOMING='87366c62d3b5c47d170f747b1cb40ab38d501013'
ENTRIES={
 93:('RA-12','c797aee814c8bebe4452329c93f5d84fd9c41f1f','d9e25009e3ce65cf864002354830bdcc286f7252'),
 103:('RA-10','6f5861fa392db467dc23abd096a02a08573146b8','494438ee01cde9ad5706537b026d85b9aab03b1b')}
checks={};results={}
def git(*args):return subprocess.check_output(['git','-C',REPO,*args])
def blob(commit,path):return git('show',commit+':'+path)
def tree(commit):
    result={}
    for line in git('ls-tree','-r','-z',commit).split(b'\0'):
        if line:
            meta,path=line.split(b'\t',1)
            mode,kind,hash=meta.decode().split()
            result[path.decode()]={'mode':mode,'kind':kind,'hash':hash}
    return result
def ck(name,condition):
    checks[name]=bool(condition)
    assert checks[name],name
incoming=tree(INCOMING)
for pr,(id,prior,latest) in ENTRIES.items():
    before=tree(prior);after=tree(latest)
    prefix=f'PR{pr}_'
    ck(prefix+'exact_reviewed_and_incoming_parents',git('show','-s','--format=%P',latest).decode().strip().split()==[prior,INCOMING])
    registry=json.loads(blob(latest,'problem_ids.json'))
    ck(prefix+'203_permanent_IDs',len(registry)==203)
    ck(prefix+'registry_identical_to_both_parents',after['problem_ids.json']==before['problem_ids.json']==incoming['problem_ids.json'])
    canonical=f'randomized-and-low-rank-approximation/{id}/'
    ref=f'references/stepaniants-{id.lower().replace("-","")}-2026-09-11'
    reference_readme=ref+'/README.md'
    canonical_files=[p for p in before if p.startswith(canonical)]
    for p in canonical_files:ck(prefix+'canonical_proof_unchanged_'+p,after.get(p)==before[p])
    for ident,path in registry.items():
        ck(prefix+'canonical_'+ident,after[path]==(before[path] if ident==id else incoming[path]))
    owned=[p for p in before if p.startswith(ref+'/') and p!=reference_readme]
    for p in owned:ck(prefix+'prior_support_unchanged_'+p,after.get(p)==before[p])
    old_readme=blob(prior,reference_readme);new_readme=blob(latest,reference_readme)
    ck(prefix+'entire_reference_README_prefix_retained',new_readme.startswith(old_readme))
    append=new_readme[len(old_readme):].decode()
    ck(prefix+'only_dated_integration_append',append.startswith('\n## Integration with accepted main') and append.count('\n## ')==1)
    record=json.loads(blob(latest,ref+'/verification/main-integration-2026-09-11-87366c6.json'))
    ck(prefix+'correct_manifest_parents',record['prior_head']==prior and record['incoming_commit']==INCOMING)
    for p,expected in record['original_proof_and_reference_hashes'].items():
        data=blob(prior,p)
        ck(prefix+'historical_fingerprint_'+p,len(data)==expected['bytes'] and hashlib.sha256(data).hexdigest()==expected['sha256'])
    for p,expected in record['current_files'].items():
        data=blob(latest,p)
        ck(prefix+'current_fingerprint_'+p,len(data)==expected['bytes'] and hashlib.sha256(data).hexdigest()==expected['sha256'])
    upstream_evidence=[p for p in incoming if p.startswith('references/') or re.search(r'/solution\.(md|tex|pdf)$',p)]
    ck(prefix+'1260_upstream_evidence_count',len(upstream_evidence)==record['upstream_proof_and_evidence_blobs_byte_identical']==1260)
    for p in upstream_evidence:ck(prefix+'upstream_blob_'+p,after.get(p)==incoming[p])
    # Every merge-tree change relative to incoming is an old reviewed PR path,
    # or one of exactly three new local integration records/verifier.
    old_base=git('merge-base',prior,INCOMING).decode().strip();baseline=tree(old_base)
    prior_changes={p for p in set(before)|set(baseline) if before.get(p)!=baseline.get(p)}
    new_delta={p for p in set(after)|set(incoming) if after.get(p)!=incoming.get(p)}
    novel=sorted(new_delta-prior_changes)
    expected_new={ref+'/verification/main-integration-2026-09-11-87366c6.'+ext for ext in ['json','md']}|{ref+'/verification/verify_main_integration.py'}
    ck(prefix+'exact_new_delta_scope',set(novel)==expected_new)
    for p in ['tools/render_problems.py','tools/solution-template.tex']:
        ck(prefix+'reviewed_tool_unchanged_'+p,after[p]==before[p])
    for p in ['tools/validate_problem_ids.py','tools/update_catalog.py','tests/test_problem_ids.py','.github/workflows/problem-ids.yml']:
        ck(prefix+'upstream_safeguard_unchanged_'+p,after[p]==incoming[p])
    # Check current catalog counts directly from unchanged canonical metadata.
    counts=collections.Counter()
    for ident,p in registry.items():
        status=re.search(rb'^\*\*Status:\*\* (.*?)\s*$',blob(latest,p),re.M).group(1).decode()
        counts[status]+=1
    expected_counts={'Open':67,'Partially resolved':74,'Solution claimed':1,'Solved':61} if pr==93 else {'Open':68,'Partially resolved':73,'Solution claimed':1,'Solved':61}
    ck(prefix+'canonical_status_counts',dict(counts)==expected_counts)
    # Resolve-list merge must leave accepted upstream text untouched except the
    # already-reviewed author's entry and the corresponding historical paragraph.
    old_resolved=blob(prior,'RESOLVED.md').decode();new_resolved=blob(latest,'RESOLVED.md').decode();upstream_resolved=blob(INCOMING,'RESOLVED.md').decode()
    subject=id+' '
    for heading in re.findall(r'^###? .+$',upstream_resolved,re.M):
        ck(prefix+'retained_upstream_resolution_heading_'+heading,heading in new_resolved)
    results[str(pr)]={'prior_reviewed_head':prior,'incoming':INCOMING,'latest_head':latest,'canonical_directory_files_unchanged':len(canonical_files),'existing_reference_files_unchanged':len(owned),'upstream_evidence_blobs_unchanged':len(upstream_evidence),'new_paths':novel,'status_counts':dict(counts),'pdfs':[{'path':p,'sha256':hashlib.sha256(blob(latest,p)).hexdigest(),'byte_identical_to_reviewed':after[p]==before[p]} for p in canonical_files if p.endswith('.pdf')],'all_claimed_historical_and_current_fingerprints':'PASS'}
report={'passed':sum(checks.values()),'total':len(checks),'checks':checks,'PRs':results,'scope':'Exact delta review. Existing full mathematical and PDF reviews carry only because source and final PDF bytes are unchanged.'}
(OUT/'PR93-103-delta-checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'passed':report['passed'],'total':report['total'],'PRs':results},indent=2))
