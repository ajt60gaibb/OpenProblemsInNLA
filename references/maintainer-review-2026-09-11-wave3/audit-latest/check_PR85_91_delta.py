"""Read-only independent merge delta verification, pinned to exact PR heads."""
import subprocess,json,hashlib,re
from pathlib import Path
CLONE='/private/tmp/nla-review-wave2-20260911'
OUT=Path(__file__).resolve().parent
INCOMING='87366c62d3b5c47d170f747b1cb40ab38d501013'
JOBS=[(85,'MI-28','58a65609730306db4004352ccbdb5d8273ca2ff4','1f9a8bbd7cce9ae429fd7fd17ff409da751c414d'),
      (91,'MI-24','cc5ed78e4ca055f15717e5130f69bff6097d9406','5d5f2a32a17c0ed7bb9fdfc976ab7af44c19dd4f')]
def git(*args):return subprocess.check_output(['git','-C',CLONE,*args])
def blob(commit,path):return git('show',commit+':'+path)
def tree(commit):
    out={}
    for line in git('ls-tree','-rz',commit).split(b'\0'):
        if not line:continue
        meta,path=line.split(b'\t',1)
        out[path.decode()]=meta.split()[2].decode()
    return out
def target(b):return b.split(b'## Problem statement\n',1)[1]
def digest(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
accepted=tree(INCOMING);report=[]
for pr,ident,old,new in JOBS:
    before,after=tree(old),tree(new)
    parents=git('show','-s','--format=%P',new).decode().strip().split()
    assert parents==[old,INCOMING]
    ref='references/stepaniants-'+ident.lower().replace('-','')+'-2026-09-11'
    recordpath=ref+'/verification/main-integration-2026-09-11-87366c6.json'
    record=json.loads(blob(new,recordpath))
    assert record['prior_head']==old and record['incoming_commit']==INCOMING
    canonical='matrix-inequalities-and-norms/'+ident+'/README.md'
    assert blob(new,canonical)==blob(old,canonical)
    assert target(blob(new,canonical))==target(blob(INCOMING,canonical))
    for p in record['original_proof_and_reference_hashes']:
        assert digest(blob(old,p))==record['original_proof_and_reference_hashes'][p]
        if p==ref+'/README.md':assert blob(new,p).startswith(blob(old,p))
        else:assert after[p]==before[p]
    for p,d in record['current_files'].items():assert digest(blob(new,p))==d,(pr,p)
    registry=blob(new,'problem_ids.json')
    assert registry==blob(old,'problem_ids.json')==blob(INCOMING,'problem_ids.json')
    ids=json.loads(registry);assert len(ids)==203
    unchanged_canonical=[];owned_hashes={}
    for other,p in ids.items():
        for suffix in ['README.md','problem.tex','problem.pdf']:
            q=str(Path(p).parent/suffix)
            if other==ident:
                assert after[q]==before[q];owned_hashes[q]=digest(blob(new,q))
            else:
                assert after[q]==accepted[q];unchanged_canonical.append(q)
    for suffix in ['solution.md','solution.tex','solution.pdf']:
        q='matrix-inequalities-and-norms/'+ident+'/'+suffix
        assert after[q]==before[q];owned_hashes[q]=digest(blob(new,q))
    evidence=[p for p in accepted if p.startswith('references/') or re.search(r'/solution\.(md|tex|pdf)$',p)]
    assert all(after[p]==accepted[p] for p in evidence)
    assert len(evidence)==record['upstream_proof_and_evidence_blobs_byte_identical']==1260
    assert len(unchanged_canonical)==606
    changed=[p for p in sorted(set(before)|set(after)) if before.get(p)!=after.get(p)]
    newcontent=[p for p in changed if after.get(p) not in {before.get(p),accepted.get(p)}]
    expected={ref+'/README.md',recordpath,ref+'/verification/main-integration-2026-09-11-87366c6.md',ref+'/verification/verify_main_integration.py',
              'README.md','CATALOG.md','RESOLVED.md','matrix-inequalities-and-norms/README.md'}
    assert set(newcontent)<=expected,(pr,newcontent)
    # The resolution list is exactly the accepted file plus this unchanged submission section.
    accepted_res=blob(INCOMING,'RESOLVED.md').decode();new_res=blob(new,'RESOLVED.md').decode();old_res=blob(old,'RESOLVED.md').decode()
    section=re.search(r'^### .*'+ident+r' .*?(?=^### |\Z)',old_res,re.M|re.S).group()
    assert section in new_res
    assert new_res.replace(section,'',1)==accepted_res
    counts={}
    for p in ids.values():
        status=re.search(r'^\*\*Status:\*\* (.+?)\s*$',blob(new,p).decode(),re.M).group(1)
        counts[status]=counts.get(status,0)+1
    assert counts=={'Open':68,'Partially resolved':73,'Solution claimed':1,'Solved':61}
    report.append({'PR':pr,'old_reviewed_head':old,'latest_head':new,'parents':parents,'result':'PASS',
       'total_changed_paths_including_incoming_main':len(changed),'new_merge_content_paths':newcontent,
       'new_or_appended_submission_records':[p for p in newcontent if p.startswith(ref)],
       'registry_mapping_count':203,'other_upstream_canonical_files_identical':len(unchanged_canonical),
       'upstream_proof_evidence_blobs_identical':len(evidence),'all_original_recorded_hashes_match':True,
       'all_current_recorded_hashes_match':True,'resolution_list_equals_accepted_plus_unchanged_owned_section':True,
       'status_counts':counts,'unchanged_canonical_and_proof_hashes':owned_hashes})
(OUT/'PR85-91-delta-evidence.json').write_text(json.dumps(report,indent=2)+'\n')
for r in report:print('PASS',r['PR'],r['latest_head'],'6 canonical/proof files unchanged;',r['other_upstream_canonical_files_identical'],'other canonical files;',r['upstream_proof_evidence_blobs_identical'],'accepted evidence blobs; all hashes and attribution preserved.')
