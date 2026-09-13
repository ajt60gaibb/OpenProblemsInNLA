"""Audit installed RA-08 candidate metadata and exact historical preservation.

Adapted with attribution to the retained IS-03 candidate protocol. This is
documentation/input auditing only: no Lean, dependency, network or Git write.
"""
from pathlib import Path
import datetime, hashlib, json, re, subprocess
import yaml

E=Path(__file__).resolve().parent;P=E.parents[1];W=P.parents[2]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
baseline=json.loads((E/'baseline.json').read_text())
archives={x['source']:P/x['archive'] for x in baseline['archive_plan']['archives_required_before_any_live_replacement']}
def historical(path):
    path=Path(path).resolve()
    for name,archive in archives.items():
        if path==(P/name).resolve():return archive
    return path
proof=json.loads((P/'verification/proof-freeze.json').read_text())
statement=json.loads((P/'reviews/statement-freeze.json').read_text())
assert len(proof['files'])==450 and len(statement['files'])==39
assert sha(P/'verification/proof-freeze.json')==baseline['proof_freeze_sha256']
assert sha(P/'reviews/statement-freeze.json')==baseline['statement_freeze_sha256']
for f in (proof,statement):
    for rel,h in f['files'].items():assert sha(historical(P/rel))==h,rel
for rel,row in baseline['original_project_inputs'].items():
    target=historical(P/rel)
    assert sha(target)==row['sha256'] and target.stat().st_size==row['bytes'],rel
originals={}
for rel,h in proof['source_files'].items():
    raw=subprocess.check_output(['git','show',proof['base']+':'+rel],cwd=W)
    assert hashlib.sha256(raw).hexdigest()==h and (W/rel).read_bytes()==raw
    blob=subprocess.check_output(['git','rev-parse',proof['base']+':'+rel],cwd=W,text=True).strip()
    assert blob==proof['source_git_blobs'][rel]
    originals[rel]={'sha256':h,'git_blob':blob}

evidence={}
for rel,expected in baseline['all_existing_evidence_manifests'].items():
    path=P/rel;assert sha(path)==expected['sha256'] and path.stat().st_size==expected['bytes']
    j=json.loads(path.read_text());assert len(j['files'])==expected['bound_files']
    redirected=[]
    for name,row in j['files'].items():
        actual=(path.parent/name).resolve()
        assert actual.is_relative_to(P.resolve())
        retained=historical(actual)
        assert sha(retained)==row['sha256'] and retained.stat().st_size==row['bytes'],(rel,name)
        if retained!=actual:redirected.append(name)
    evidence[rel]={**expected,'all_bound_bytes_preserved':True,'wrapper_archive_redirects':redirected}
assert len(evidence)==6

metadata=yaml.safe_load((P/'formalization.yaml').read_text())
cfg=json.loads((P/'comparator.json').read_text())
names=cfg['theorem_names'];axioms=['propext','Classical.choice','Quot.sound']
challenge=(P/'Challenge.lean').read_text();solution=(P/'Solution.lean').read_text()
def signatures(text):
    return {n:' '.join(s.split()) for n,s in re.findall(r'^theorem\s+(\w+)(.*?)\s*:=\s*by\b',text,re.M|re.S)}
assert signatures(challenge)==signatures(solution)
assert names==['NLA.RA08.'+n for n in signatures(solution)] and len(names)==14
assert cfg['definition_names']==[] and cfg['permitted_axioms']==axioms
assert [x['declaration'] for x in metadata['status']['main_results']]==names
assert [x['declaration'] for x in metadata['alignment']]==names
assert metadata['status']['sorry_count']==metadata['status']['sorry_in_definitions']==0
assert metadata['status']['axioms']==axioms
assert metadata['project']['authors']==['George Stepaniants']
assert metadata['project']['affiliations']['George Stepaniants']==(
    'Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA')
assert metadata['sources'][1]['title']=='Concave matrix-function error transfer can fail for exact Nyström approximations'
assert metadata['sources'][1]['authors']==['Matthew J. Colbrook']
assert metadata['review']['linux_verification']['status']=='pending'
for group in ['statement_reports','proof_reports']:
    assert len(metadata['review'][group])==2
    for row in metadata['review'][group]:assert sha(P/row['file'])==row['sha256']
for group in ['statement_report_evidence','proof_report_evidence']:
    assert len(metadata['review'][group])==2
    for rel,row in metadata['review'][group].items():
        assert sha(P/rel)==row['sha256'] and (P/rel).stat().st_size==row['bytes']
for group in ['statement_freeze','proof_freeze','coordinator_acceptance','historical_readme','historical_formalization']:
    row=metadata['review'][group];assert sha(P/row['file'])==row['sha256']
assert sha(P/'verification/final-review-acceptance.json')==baseline['coordinator_acceptance_sha256']

links=[]
for link in re.findall(r'\]\(([^)]+)\)',(P/'README.md').read_text()):
    assert (P/link.split('#',1)[0]).resolve().exists(),link
    links.append(link)
for n in ['README.md','formalization.yaml']:
    text=(P/n).read_text()
    assert text.endswith('\n') and not any(x.rstrip()!=x for x in text.splitlines())
    assert not re.search(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',text)
    assert sha(P/n)==baseline['archive_plan']['draft_'+('readme' if n=='README.md' else 'metadata')+'_sha256']
    assert sha(P/n)!=sha(archives[n])
assert 'defaultTargets = ["Challenge"]' in (P/'lakefile.toml').read_text()
assert '[[lean_lib]]\nname = "Solution"' in (P/'lakefile.toml').read_text()

checks=json.loads((E/'validation-checks.json').read_text())
assert len(checks['commands'])==3 and checks['all_exit_zero']
for row in checks['commands']:
    assert row['exit_code']==0 and sha(E/row['log'])==row['log_sha256']
assert 'PASS (14 declarations)' in (E/'manifest.log').read_text()
assert 'Validated 217 permanent problem IDs against origin/main' in (E/'permanent-ids-origin.log').read_text()
assert 'Validated 217 permanent problem IDs against nla-upstream/main' in (E/'permanent-ids-upstream.log').read_text()
assert 'Ran 17 tests' in (P/'verification/final/permanent-id-tests.log').read_text()
assert len(json.loads((W/'problem_ids.json').read_text()))==217
assert sha(W/'problem_ids.json')==baseline['registry_sha256']
assert '**Status:** Solved' in (P.parent/'README.md').read_text()
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=W,text=True).strip()==baseline['base']
assert not subprocess.check_output(['git','diff','--name-only'],cwd=W)
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=W)
actual_author=json.loads((P/'verification/final/attempt-wf0an4vo/result.json').read_text())
assert actual_author['verdict']=='PASS' and len(actual_author['commands'])==19
author_log=P/'verification/final/attempt-wf0an4vo/verification-final-Inspect.log'
# The completion report and full proof freeze already bind all author logs;
# metadata packaging reads that immutable result without rerunning any proof.
record={
    'verdict':'PASS installed candidate packaging and exact complete input preservation',
    'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'role':'/root/leancert_examples; prior independent final referee 1, now separate documentation/input preparer; no extra mathematical referee',
    'base':baseline['base'],'project':str(P),
    'prepackaging_project_inputs':len(baseline['original_project_inputs']),
    'unchanged_prepackaging_nonwrapper_inputs':len(baseline['original_project_inputs'])-2,
    'proof_inputs_preserved_using_exact_archives':450,'other_proof_inputs_byte_identical':448,
    'statement_inputs_preserved_using_exact_archives':39,'other_statement_inputs_byte_identical':37,
    'original_source_Git_blobs_unchanged':originals,
    'all_existing_evidence_inventories':evidence,
    'historical_archives':{str(p.relative_to(P)):sha(p) for p in archives.values()},
    'current_wrappers':{n:sha(P/n) for n in ['README.md','formalization.yaml']},
    'complete_advertised_exports':names,'definition_exceptions':[],'permitted_axioms':axioms,
    'actual_metadata_schema_and_export_coverage':'PASS (14 declarations)',
    'permanent_ID_validation':'PASS: 217 unchanged IDs against origin/main and nla-upstream/main',
    'prior_permanent_ID_tests':'17 passed; sealed historical result retained, no repeated test for wrapper-only edits',
    'all_README_links_resolve':links,
    'author_checks_read_without_rerun':{'commands':19,'printed_standard_three_reports':59},
    'final_referee_checks_read_without_rerun':{'referee1':{'commands':20,'standard_three_reports':61},'referee2':{'commands':19,'standard_three_reports':62}},
    'all_canonical_registry_catalog_tracked_files':'unchanged; no regeneration required',
    'proof_dependency_build_download_cache_or_source_change':False,
    'only_historical_wrapper_replacements':['README.md','formalization.yaml'],
    'only_other_additions':'two exact historical archives and this candidate packaging evidence',
    'canonical_status':'Solved, unchanged','Linux_Comparator_default_kernel_real_controls':'pending',
    'independent_operational_and_publication_acceptance':'pending','commit_or_push':False,
}
(E/'integrity.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'verdict':record['verdict'],'integrity_sha256':sha(E/'integrity.json'),
    'prepackaging_inputs':record['prepackaging_project_inputs'],'unchanged_nonwrappers':record['unchanged_prepackaging_nonwrapper_inputs'],
    'manifest_bound_counts':{n:r['bound_files'] for n,r in evidence.items()}},indent=2))
