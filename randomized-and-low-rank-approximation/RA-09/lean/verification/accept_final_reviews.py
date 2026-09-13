from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, re

R=Path('/tmp/nla-lean-ra09-worktree')
P=R/'randomized-and-low-rank-approximation/RA-09/lean'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(f):
    d=json.loads(f.read_text());base=f.parent
    for r,v in d['files'].items():
        p=base/r;want=v if isinstance(v,str) else v['sha256']
        assert h(p)==want,(f,r)
        if isinstance(v,dict) and 'bytes' in v:assert p.stat().st_size==v['bytes']
    actual={str(p.relative_to(base)) for p in base.rglob('*') if p.is_file() and p!=f}
    internal={r for r in d['files'] if not r.startswith('../')}
    assert actual==internal,(f,actual-internal,internal-actual)
    return dict(path=str(f.relative_to(P)),sha256=h(f),bound_files=len(d['files']))

freeze=P/'verification/proof-freeze.json';f=json.loads(freeze.read_text())
assert h(freeze)=='533f5c328cdaf8c1f23f238f8c71b7b4b2fdabb2f532d58a398d4ab2434ccf7e'
statement=P/'reviews/statement-freeze.json';s=json.loads(statement.read_text())
for record in [f,s]:
    for r,v in record['files'].items():assert h(P/r)==v,r
for r,v in f['source_files'].items():
    assert h(R/r)==v,r
    blob=subprocess.check_output(['git','show',f['base']+':'+r],cwd=R)
    assert hashlib.sha256(blob).hexdigest()==v,r
    assert subprocess.check_output(['git','rev-parse',f['base']+':'+r],cwd=R,text=True).strip()==f['source_git_blobs'][r]
prior=[inventory(P/r) for r in f['nested_evidence_manifests_bound']]
reviews=[]
for n,who,report_sha,expected_success,expected_fail,expected_axioms in [
    (1,'/root/ra09_final_referee1','c967a8a02b5d731fa9c0c940c6c3b022a9881c792ec1c5676b2d1f06aeec8c4f',18,0,66),
    (2,'/root/mf16_final_referee','bfbfd8c1377c149deac4b8784304a7484e1d6156368d0c2cf488ddae47a9dd97',19,1,50)]:
    report=P/f'reviews/final-referee-{n}.md';assert h(report)==report_sha
    E=P/f'reviews/final-referee-{n}-evidence'
    inv=inventory(E/'EVIDENCE-MANIFEST.json')
    result_names=['execution.json'] if n==1 else ['fresh-result.json','resume-result.json']
    rows=[];report_count=0
    for name in result_names:
        r=json.loads((E/name).read_text())
        for c in r['commands']:
            log=E/c['log'];raw=log.read_text()
            if 'log_sha256' in c:assert h(log)==c['log_sha256']
            src_hash=c.get('source_sha256',c.get('sha256'))
            if 'source_snapshot' in c:assert h(E/c['source_snapshot'])==src_hash
            elif c['exit_code']==0:assert h(P/c['source'])==src_hash
            if c['exit_code']==0:
                for ax in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',raw):
                    names={x.strip() for x in ax.split(',') if x.strip()}
                    assert names <= {'propext','Classical.choice','Quot.sound'},(name,c['source'],names)
                    report_count+=1
            rows.append(c)
    success=sum(c['exit_code']==0 for c in rows);failed=len(rows)-success
    assert (success,failed,report_count)==(expected_success,expected_fail,expected_axioms),(n,success,failed,report_count)
    reviews.append(dict(reviewer=who,report=str(report.relative_to(P)),sha256=report_sha,evidence=inv,successful_direct_source_commands=success,retained_failed_Lean_commands=failed,actual_standard_three_reports=report_count,mathematical_revision_requested=False,diagnostics='Reviewer-only parser correction; no Lean failure' if n==1 else 'Reviewer-only import-order failure and successful correction, complete raw attempts retained'))

gate=dict(utc=datetime.now(timezone.utc).isoformat(),gate='ACCEPT both independent final mathematical approvals; candidate packaging and actual Linux may proceed',coordinator='/root',coordinator_role='Disclosed Frobenius, zero-column and zero-tail implementation coauthor; not an independent final mathematical referee',reviewed_proof_freeze_sha256=h(freeze),statement_freeze_sha256=h(statement),project_inputs_preserved=len(f['files']),statement_inputs_preserved=len(s['files']),original_source_Git_blobs_preserved=len(f['source_files']),prior_complete_inventories=prior,reports=reviews,root_review='Both complete final mathematical reports, all seventeen actual Solution contracts, main Proof and complete proof map read; exact original statement boundary previously independently reviewed and generic helpers implemented under disclosed roles. Complete frozen bytes, original Git identities, all seven prior inventories and both complete final-referee inventories rehashed. Actual successful command/log identities and all 66/50 standard-three report contents independently checked.',scope='Full original real PSD-order affirmative trace-deficit implication, all half-line continuous concave nondecreasing nonnegative functions including f(0)>0, all original dimensions/ranks/nonnegative epsilon and every permitted ordered eigenbasis. Actual Frobenius norm, CFC, trace, scalar, harmonic, overlap and zero/positive-tail bridges are proved.',numerical_scope='Pure exact unbounded scalar and finite matrix reasoning. Actual LeanCert kernel assertions, no interval certificate or numerical oracle.',nonblocking_finding='OrderedExistence.lean copied header says counterexample for an affirmative theorem. Preserve frozen comment bytes; disclose the typo in live candidate README. Historical phase documents remain intact and are identified as historical.',required_next_steps=['Archive exact frozen README and install truthful candidate README and v0.4 formalization.yaml','Independent concrete candidate packaging review and blank-email commit/push','Actual non-root Ubuntu Comparator, default-kernel replay and real controls','Independent operational review; canonical publication/index/PDF checks; separate upstream PR'],canonical_status='Solved, unchanged',actual_Linux_Comparator='pending',publication='pending')
G=P/'verification/final-review-acceptance.json';assert not G.exists();G.write_text(json.dumps(gate,indent=2)+'\n')
(P/'verification/accept_final_reviews.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({'gate_sha256':h(G),'reviews':reviews,'preserved_project':len(f['files']),'preserved_statement':len(s['files']),'preserved_originals':len(f['source_files'])},indent=2))
