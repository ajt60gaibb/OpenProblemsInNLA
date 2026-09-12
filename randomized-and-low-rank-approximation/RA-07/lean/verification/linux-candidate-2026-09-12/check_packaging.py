"""Packaging-only identity and metadata checks for the reviewed RA-07 candidate.
Does not edit mathematical sources or run/claim Linux verification. Earlier
successful validator/test outputs were retained verbatim from tool stdout.
"""
from pathlib import Path
import datetime, hashlib, json, re, subprocess
import yaml
OUT=Path(__file__).resolve().parent
PROJECT=OUT.parents[1]
REPO=PROJECT.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*args):return subprocess.check_output(['git','-C',str(REPO),*args]).decode().strip()
def save(name,data):(OUT/name).write_text(json.dumps(data,indent=2)+'\n')
assert git('rev-parse','HEAD')=='8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc'
assert not git('diff','--name-only') and not git('diff','--cached','--name-only')
old=json.loads((OUT/'inputs-before.json').read_text())['files']
unchanged={}
for rel,rec in old.items():
    current=sha(PROJECT/rel)
    if rel=='README.md':
        assert current!=rec['sha256']
        assert sha(OUT/'frozen-statement-stage-README.md')==rec['sha256']
    else:
        assert current==rec['sha256'],rel
        unchanged[rel]=current
freeze_path=PROJECT/'verification/proof-freeze.json'
assert sha(freeze_path)=='ecd94daf2dee9fe4625e09f1a08026eb75ac8a14bea6efb688921a3e78eb6b4a'
freeze=json.loads(freeze_path.read_text())
assert len(freeze['files'])==38
for rel,rec in freeze['files'].items():
    actual=OUT/'frozen-statement-stage-README.md' if rel=='README.md' else PROJECT/rel
    assert sha(actual)==rec['sha256'] and actual.stat().st_size==rec['bytes'],rel
for rel,rec in freeze['original_sources'].items():
    b=subprocess.check_output(['git','-C',str(REPO),'show',freeze['source_commit']+':'+rel])
    assert (REPO/rel).read_bytes()==b and hashlib.sha256(b).hexdigest()==rec['sha256'],rel
config=json.loads((PROJECT/'comparator.json').read_text())
meta=yaml.safe_load((PROJECT/'formalization.yaml').read_text())
assert meta['version']=='v0.4'
assert meta['review']['linux_verification']['status']=='pending'
assert meta['review']['status'].endswith('Linux Comparator pending')
assert meta['status']['sorry_count']==meta['status']['sorry_in_definitions']==0
assert 'Canonical status remains Solved.' in meta['status']['scope']
assert config['definition_names']==[]
assert config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
assert [r['declaration'] for r in meta['status']['main_results']]==config['theorem_names']
assert len(config['theorem_names'])==6
for group in ['statement_reports','proof_reports']:
    assert len(meta['review'][group])==2
    for r in meta['review'][group]:assert sha(PROJECT/r['file'])==r['sha256'],r['file']
assert sha(PROJECT/'reviews/proof-referee-1.md')=='3b232fe78975ae885909a7e805686e32db0b4db9e65760502a55795460d398e3'
assert sha(PROJECT/'reviews/proof-referee-2.md')=='23f5e33d7992bcf204a183b6a71f634e029ed0cc0b06a8e85bedfe35c06046c8'
assert 'interval calculation' in meta['automation']['methods'][0]['prompting_notes']
assert 'no claimed numerical certificate' in meta['automation']['methods'][0]['prompting_notes']
assert sha(REPO/'docs/lean/schema/v0.4.schema.json')=='25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce'
readme=(PROJECT/'README.md').read_text()
assert not any(ord(c)<32 and c not in '\n\t' for c in readme)
links=[]
for target in re.findall(r'\]\(([^)]+)\)',readme):
    if target.startswith(('https://','http://','#')):continue
    link=(PROJECT/target.split('#')[0]).resolve()
    assert link.is_file(),target
    links.append(target)
assert not re.search(r'[A-Za-z0-9_.+\-]+@[A-Za-z0-9.\-]+',(PROJECT/'formalization.yaml').read_text()+readme)
manifest=json.loads((PROJECT/'lake-manifest.json').read_text())
deps=[]
for d in manifest['packages']:
    folder=PROJECT/'.lake/packages'/d['name']
    head=subprocess.check_output(['git','-C',str(folder),'rev-parse','HEAD']).decode().strip()
    status=subprocess.check_output(['git','-C',str(folder),'status','--porcelain']).decode().strip()
    assert head==d['rev'] and not status,d['name']
    deps.append({'name':d['name'],'revision':head,'status':status})
assert len(deps)==10
save('dependency-check.json',deps)
paths=git('ls-files','--others','--exclude-standard','--',str(PROJECT.relative_to(REPO))).splitlines()
for rel in paths:
    assert not (REPO/rel).is_symlink(),rel
    assert '.lake/' not in rel and '.verification/' not in rel,rel
    assert not re.search(r'\.(olean|ilean|trace|pyc)(\.|$)',rel),rel
commands=[
 {'argv':['/tmp/nla-lean-formalization/venv/bin/python','tools/lean/validate_manifest.py',str(PROJECT.relative_to(REPO))],'exit_code':0,'log':'metadata-validation.log'},
 {'argv':['python3','tools/validate_problem_ids.py','--base-ref','origin/main'],'exit_code':0,'log':'permanent-ids.log'},
 {'argv':['python3','-m','unittest','discover','-s','tests','-p','test_problem_ids.py','-v'],'exit_code':0,'log':'permanent-id-tests.log'}]
assert (OUT/'metadata-validation.log').read_text()=='Manifest schema and comparator coverage: PASS (6 declarations)\n'
assert (OUT/'permanent-ids.log').read_text()=='Validated 217 permanent problem IDs against origin/main\n'
assert 'Ran 17 tests in ' in (OUT/'permanent-id-tests.log').read_text()
assert (OUT/'permanent-id-tests.log').read_text().endswith('\nOK\n')
for c in commands:c['log_sha256']=sha(OUT/c['log']);c['cwd']=str(REPO);c['capture']='Verbatim combined tool stdout; no test or proof execution inferred from this metadata check.'
record={'verdict':'PASS for root review of a Linux candidate; actual Linux verification remains pending','packager':'solved_statement_inventory','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'branch':git('rev-parse','--abbrev-ref','HEAD'),'base_commit':git('rev-parse','HEAD'),'permanent_id_validation_base':git('rev-parse','origin/main'),'original_publishable_input_count':len(old),'unchanged_original_inputs':unchanged,'authorized_historical_readme_update':{'frozen_sha256':old['README.md']['sha256'],'archived_as':'verification/linux-candidate-2026-09-12/frozen-statement-stage-README.md','current_sha256':sha(PROJECT/'README.md')},'formalization_yaml_sha256':sha(PROJECT/'formalization.yaml'),'all_37_remaining_freeze_inputs_unchanged':True,'all_prior_review_and_evidence_bytes_unchanged':True,'three_original_source_hashes':freeze['original_sources'],'proof_freeze_sha256':sha(freeze_path),'statement_review_hashes':meta['review']['statement_reports'],'final_review_hashes':meta['review']['proof_reports'],'exports':config['theorem_names'],'lean_cert_role':'Explicit kernel trust audit for exact algebra/root geometry; no interval calculation or numerical certificate claimed.','metadata_and_required_checks':commands,'readme_links_checked':links,'clean_dependency_pins':10,'existing_artifact_exclusions_preserved':True,'tracked_and_staged_diff_empty':True,'canonical_status':'Solved, byte-identical','shared_harness_unchanged':True,'scope':'Packaging only. No mathematical source, proof, configuration, original source, ID, shared harness or prior evidence changed. No catalog regeneration, commit, push, PR or Linux run performed.'}
save('packaging-record.json',record)
print('PASS: metadata, six exports, all 37 non-README freeze inputs, prior evidence, source/ID identity, ten clean pins and links; Linux pending.')
