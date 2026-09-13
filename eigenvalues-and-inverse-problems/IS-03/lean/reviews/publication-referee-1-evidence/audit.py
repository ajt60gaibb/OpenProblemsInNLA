"""Independent IS-03 publication identity/content inspection by leancert_examples.

Reads the actual final package, frozen source and prior execution. No source,
metadata, Lean, render, cache, Git history or publication mutation. The original
preparer seal remains immutable; a later bounded wording revision is separate.
"""
from pathlib import Path
import json,hashlib,re,subprocess,datetime,collections
import yaml
P=Path(__file__).resolve().parents[2];W=P.parents[2];E=Path(__file__).resolve().parent
D=P/'verification/publication-2026-09-12'
R=P/'verification/publication-scope-correction-2026-09-12'
CAND='f87375fa5d7926fe0e065199eaab8f15ac5a5e48'
BASE='5830ed4fb06da0659414a3deb2a40ad327aca052'
HEAD='ab164900f806ab7208ca8b0107a6238603eaacad'
PR='eigenvalues-and-inverse-problems/IS-03/lean'
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git','-C',str(W),*a])
def read(p):return Path(p).read_bytes()
def save(n,j):(E/n).write_text(json.dumps(j,indent=2)+'\n')
assert git('rev-parse','HEAD').decode().strip()==HEAD
assert sha(read(D/'EVIDENCE-MANIFEST.json'))=='f01c38486feff1079f6366dd22e2b39437453d1b3040e102f1318876b1133b97'
assert sha(read(D/'PUBLICATION-HANDOFF.md'))=='56f6ef7249a2e364117ed1a576c0c341791460ae9090def5557aca57addb53d8'
assert sha(read(D/'INTEGRITY-CHECKS.json'))=='8c2123242a0c56ccc78943c8b5cbfd21095d2ef0c2e6877bf8e69c220ac51d26'
def check_manifest(path,complete=True):
    j=json.loads(path.read_text());files=j['files']
    actual={str(p.relative_to(path.parent)) for p in path.parent.rglob('*') if p.is_file() and p!=path}
    if complete:assert actual=={r for r in files if not r.startswith('../')},str(path)
    for r,v in files.items():
        q=(path.parent/r).resolve();assert q.is_relative_to(P.resolve())
        assert sha(q.read_bytes())==v['sha256'] and q.stat().st_size==v['bytes'],r
    return len(files)
assert check_manifest(D/'EVIDENCE-MANIFEST.json')==35
before=json.loads((D/'before.json').read_text());integrity=json.loads((D/'INTEGRITY-CHECKS.json').read_text())
assert sha(read(R/'EVIDENCE-MANIFEST.json'))=='4b996130f6e42faa97e7960b9041d0f7a026e64cb4c71bdef66047eb6d2044ca'
assert sha(read(R/'CORRECTION.json'))=='10a2d7e8557e656ccd5472131e51d90000505a8fd77bf9e7f7cc33a3616c49ae'
assert check_manifest(R/'EVIDENCE-MANIFEST.json')==10
correction=json.loads((R/'CORRECTION.json').read_text())
assert len(correction['changes'])==2
assert correction['initial_publication_manifest_sha256']==sha(read(D/'EVIDENCE-MANIFEST.json'))
assert correction['initial_publication_integrity_sha256']==sha(read(D/'INTEGRITY-CHECKS.json'))
for change in correction['changes']:
    old_snapshot=read(R/(Path(change['file']).name+'.before.txt'))
    new_snapshot=read(R/(Path(change['file']).name+'.after.txt'))
    assert sha(old_snapshot)==change['before_sha256']==integrity['publication_sha256'][change['file']]
    assert sha(new_snapshot)==change['after_sha256'] and new_snapshot==read(W/change['file'])
    assert old_snapshot.count(change['before'].encode())==1
    assert old_snapshot.replace(change['before'].encode(),change['after'].encode())==new_snapshot
assert len(correction['current_publication_sha256'])==9
for rel,h in correction['current_publication_sha256'].items():assert sha(read(W/rel))==h
assert len(correction['checks'])==3
for row in correction['checks']:
    assert row['exit_code']==0 and sha(read(R/row['log']))==row['log_sha256']
assert (R/'manifest.log').read_text().strip()=='Manifest schema and comparator coverage: PASS (7 declarations)'
assert before['candidate']==CAND and before['upstream']==BASE and before['integration']==HEAD
receipt=json.loads(next((P/'verification/linux-2026-09-12/artifacts/lean-IS-03').glob('verify-*/result.json')).read_text())
assert before['candidate_inputs']==receipt['input_sha256'] and len(receipt['input_sha256'])==303
arch={'README.md':'archive/README.linux-candidate.md','formalization.yaml':'archive/formalization.linux-candidate.yaml'}
for rel,digest in receipt['input_sha256'].items():
    b=git('show',CAND+':'+PR+'/'+rel)
    assert sha(b)==digest and b==git('show',HEAD+':'+PR+'/'+rel)
    now=read(D/arch[rel]) if rel in arch else read(P/rel)
    assert now==b,(rel,'candidate identity')
assert len(integrity['unchanged_nonwrapper_sha256'])==301
for rel,digest in integrity['unchanged_nonwrapper_sha256'].items():assert sha(read(P/rel))==digest
assert len(before['operational_evidence'])==452
for rel,digest in before['operational_evidence'].items():assert sha(read(P/rel))==digest
ops=P/'verification/linux-2026-09-12';root=P/'verification/root-operational-2026-09-12'
assert check_manifest(ops/'EVIDENCE-MANIFEST.json')==444
assert check_manifest(root/'EVIDENCE-MANIFEST.json')==6
assert len([p for p in ops.rglob('*') if p.is_file()])==445
assert len([p for p in root.rglob('*') if p.is_file()])==7
rootcheck=json.loads((root/'ROOT-CHECKS.json').read_text())
assert rootcheck['status'].startswith('APPROVE') and rootcheck['candidate']==CAND and rootcheck['run']==34728101436
assert rootcheck['all_evidence_files_verified']==444 and rootcheck['matched_candidate_inputs']==303
assert sha(read(root/'ROOT-CHECKS.json'))=='f1a0d3936711ed76c006d7f59c62dd227f3a52812567578fafa284d8aa7bf154'
assert sha(read(ops/'OPERATIONAL-REVIEW.md'))=='97d43157105cc4abe654c5cd222a2e7928028d2f687f04ee3435ef6c589aff1f'
assert sha(read(ops/'EVIDENCE-MANIFEST.json'))=='66d3eef4f5a6b67f9d9aec94187af141cdda626b8c6d88b9b5c8e8e82c8ccd14'
archive='verification/linux-candidate-2026-09-12/README.statement.md'
for rel,n in [('verification/proof-freeze.json',203),('reviews/statement-freeze.json',34)]:
    j=json.loads((P/rel).read_text());assert len(j['files'])==n
    for r,h in j['files'].items():assert sha(read(P/(archive if r=='README.md' else r)))==h
    assert len(j['source_files'])==10
    for r,h in j['source_files'].items():
        snapshot=ops/'source'/r
        assert sha(snapshot.read_bytes())==h and snapshot.read_bytes()==git('show',CAND+':'+r)
        if r not in ['eigenvalues-and-inverse-problems/IS-03/README.md','eigenvalues-and-inverse-problems/IS-03/problem.tex']:
            assert read(W/r)==snapshot.read_bytes()
for label,count in [('statement-referee-1',23),('statement-referee-2',26),('proof-referee-1',36),('proof-referee-2',45)]:
    assert check_manifest(P/'reviews'/(label+'-evidence')/'EVIDENCE-MANIFEST.json')==count
# Original canonical target/reference/audit suffix is untouched, including all quantifiers.
canonical=W/'eigenvalues-and-inverse-problems/IS-03/README.md'
old=git('show',BASE+':'+str(canonical.relative_to(W))).decode();current=canonical.read_text()
assert current[current.index('## Problem statement'):]==old[old.index('## Problem statement'):]
assert sha(current[current.index('## Problem statement'):].encode())==before['canonical_target_tail_sha256']
registry=json.loads((W/'problem_ids.json').read_text())
assert len(registry)==217 and read(W/'problem_ids.json')==git('show',BASE+':problem_ids.json')
assert sha(read(W/'problem_ids.json'))==before['problem_ids_sha256']
counts=collections.Counter();prior=[]
for ident,rel in registry.items():
    data=read(W/rel);status=re.search(r'^\*\*Status:\*\* ([^\n]+)',data.decode(),re.M).group(1).strip()
    counts[status]+=1
    if ident!='IS-03':
        assert sha(data)==before['other_canonical'][ident] and data==git('show',BASE+':'+rel)
        if status=='Lean verified':prior.append(ident)
assert dict(counts)=={'Lean verified':17,'Solved':75,'Open':53,'Partially resolved':72}
assert set(prior)==set(integrity['prior_Lean_verified_entries_unchanged']) and len(prior)==16
oldres=git('show',BASE+':RESOLVED.md').decode();newres=(W/'RESOLVED.md').read_text()
def parts(s):
    start=s.index('#### IS-03 —');end=s.index('\n#### SP-06',start)
    return s[:start],s[start:end],s[end:]
a,b,c=parts(oldres);d,e,f=parts(newres);assert a==d and c==f
assert 'George Stepaniants' in e and 'Matthew J. Colbrook' in e
save('IS-03-RESOLVED-block.json',{'original':b,'current':e,'all_other_shared_group_and_registry_blocks_unchanged':True})
# Only five actual YAML fields may differ from the executed candidate.
prior_yaml=yaml.safe_load((D/'archive/formalization.linux-candidate.yaml').read_text())
now_yaml=yaml.safe_load((P/'formalization.yaml').read_text())
def diffs(a,b,path=()):
    if isinstance(a,dict) and isinstance(b,dict):
        assert set(a)==set(b),(path,'key set')
        return sum((diffs(a[k],b[k],path+(k,)) for k in a),[])
    return [] if a==b else ['.'.join(path)]
changed=diffs(prior_yaml,now_yaml)
allowed=['status.scope','review.status','review.notes','review.linux_verification.status','review.linux_verification.note']
assert set(changed)==set(allowed)
config=json.loads((P/'comparator.json').read_text())
assert config==receipt['config'] and len(config['theorem_names'])==7 and config['definition_names']==[]
assert [r['declaration'] for r in now_yaml['status']['main_results']]==config['theorem_names']
for r in now_yaml['status']['main_results']:
    assert r['axioms']==config['permitted_axioms'] and r['sorry_count']==0 and r['comparator_config']=='comparator.json'
assert now_yaml['status']['sorry_count']==now_yaml['status']['sorry_in_definitions']==0
assert 'has no entrywise-nonnegative order-six realization' in now_yaml['status']['scope']
assert 'entrywise-nonnegative' in e[e.index('impossibility'):e.index('impossibility')+120]
# All read-facing credits and actual-evidence scope remain explicit.
aff='Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'
for text in [current,(P/'README.md').read_text(),e]:
    normalized=' '.join(text.split());assert 'George Stepaniants' in normalized and aff in normalized
    assert 'Matthew J. Colbrook' in normalized and '34728101436' in normalized and CAND in normalized
    assert 'zero-padding' in text or 'zero padding' in text
    assert not re.search(r'George[^\n]*[\w.+-]+@[\w.-]+',text,re.I)
    assert 'mathematical referee' in text
assert now_yaml['project']['affiliations']['George Stepaniants']==aff
assert 'sgstepaniants/OpenProblemsInNLA/actions/runs/34728101436' in now_yaml['review']['linux_verification']['note']
# All nine actual changed tracked paths; proof files are not among them.
changed_files=git('diff','--name-only').decode().splitlines()
assert set(changed_files)==set(integrity['changed_tracked_files']) and len(changed_files)==9
mutable={'RESOLVED.md',PR+'/formalization.yaml'}
for rel,h in integrity['publication_sha256'].items():
    if rel not in mutable:assert sha(read(W/rel))==h
pres=json.loads((D/'preserved-upstream-files.json').read_text())
assert pres['base']==BASE and len(pres['Git_blobs'])==pres['file_count']==6967
for rel,blob in pres['Git_blobs'].items():
    data=read(W/rel)
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==blob,rel
# Read and verify every prior actual check's raw log; do not re-run rendering/tests.
checks=json.loads((D/'checks.json').read_text())
for row in checks:
    assert row['exit_code']==0 and sha(read(D/row['log']))==row['log_sha256']
assert (D/'manifest.log').read_text().strip()=='Manifest schema and comparator coverage: PASS (7 declarations)'
assert 'Ran 17 tests' in (D/'permanent-id-tests.log').read_text() and 'OK' in (D/'permanent-id-tests.log').read_text()
(E/'publication.diff').write_bytes(git('diff','--','CATALOG.md','README.md','RESOLVED.md','eigenvalues-and-inverse-problems'))
read_paths=[canonical,P/'README.md',P/'formalization.yaml',P/'comparator.json',W/'RESOLVED.md',W/'problem_ids.json',
 D/'PUBLICATION-HANDOFF.md',D/'INTEGRITY-CHECKS.json',D/'EVIDENCE-MANIFEST.json',D/'VISUAL-REVIEW.json',D/'before.json',D/'checks.json',D/'preserved-upstream-files.json',root/'ROOT-CHECKS.json',root/'EVIDENCE-MANIFEST.json',ops/'OPERATIONAL-REVIEW.md',ops/'EVIDENCE-MANIFEST.json']
read_paths.extend([D/row['log'] for row in checks])
read_paths.extend([R/p for p in ['CORRECTION.json','EVIDENCE-MANIFEST.json','SCOPE-CORRECTION.md','correct_scope.py','formalization.yaml.before.txt','formalization.yaml.after.txt','RESOLVED.md.before.txt','RESOLVED.md.after.txt']])
read_paths.extend([R/row['log'] for row in correction['checks']])
save('read-inputs.json',{str(f.relative_to(W)):{'sha256':sha(read(f)),'bytes':f.stat().st_size} for f in read_paths})
save('audit-result.json',{'result':'PASS independent publication content/source identity checks on final corrected state','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integration_HEAD':HEAD,'candidate':CAND,'base':BASE,'candidate_inputs':303,'nonwrapper_inputs_unchanged':301,'proof_inputs_preserved':203,'statement_inputs_preserved':34,'original_source_snapshots':10,'operational_inputs_unchanged':452,'preparer_seal_files':35,'correction_seal_files':10,'resolved_editorial_finding':'The author separately qualified two realization descriptions by entrywise nonnegativity. Exact single replacements, original sealed package, before/after snapshots and three successful fresh metadata/format checks verified. No mathematical change.','original_registry_IDs':217,'other_canonical_pages_unchanged':216,'prior_Lean_verified_preserved':16,'counts':dict(counts),'upstream_unaffected_files_preserved':6967,'only_IS03_RESOLVED_subsection_changed':True,'actual_yaml_changed_fields':changed,'actual_changed_files':changed_files,'review_role':'Independent publication reviewer, neither publication author nor IS03 proof/statement author. Prior independent statement/final referee1 and operational reviewer, no additional mathematical referee.','new_tests_builds_renders_or_source_mutations':False})
print('PASS complete corrected publication identities, exact five-field manifest scope, full target/credits, 303candidate/452ops/217IDs/6967upstream preservation; original and supplementary correction seals bound.')
