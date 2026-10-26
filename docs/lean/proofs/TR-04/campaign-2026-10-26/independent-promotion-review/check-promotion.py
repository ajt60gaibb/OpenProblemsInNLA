#!/usr/bin/env python3
"""Source-only review of a frozen, unapplied metadata/display promotion."""
from pathlib import Path
from datetime import datetime,timezone
import contextlib,difflib,hashlib,importlib.util,io,json,re,shutil,subprocess,sys

B=Path(__file__).resolve().parent;REPO=B.parents[5]
DOC=REPO/'docs/lean/proofs/TR-04';C=DOC/'campaign-2026-10-26'
P=C/'promotion-draft';CANON=REPO/'tensor-computations/TR-04/lean'
HEAD='027aaefbadf602ac460d0cf4cae7beed3181d712'
artifacts={}
def sha(p):
    assert p.is_file() and not p.is_symlink(),str(p)
    return hashlib.sha256(p.read_bytes()).hexdigest()
def bind(p,h=None):
    actual=sha(p)
    if h is not None:assert actual==h,str(p)
    artifacts[str(p.relative_to(REPO))]=actual
    return actual
def read(p,h=None):bind(p,h);return json.loads(p.read_text())
def blob(path):return subprocess.check_output(['git','show',HEAD+':'+path],cwd=REPO)

proposal=read(P/'PROMOTION_PROPOSAL.json','c352fedca0c34cf23c89e41fdc82cb870ff552b5d50c6fe01a1fc6b5d47a11b0')
assert proposal['revision']==2
prior=read(REPO/proposal['prior_proposal_preserved']['path'],'ee03f187e19741894e487547220365af7fc8274d987fb0dc105d5cc2c722bdcf')
for x in prior['proposed_replacements']:bind(P/'initial-pending-wording/input-candidate'/Path(x['proposed_path']).name,x['proposed_sha256'])
bind(B/'check-promotion-before-proposal-revision-2.py');bind(B/'proposal-revision-diagnostic.json')
assert proposal['phase']=='proposed descriptive promotion, not yet applied'
assert proposal['candidate_source_commit']==HEAD
assert len(proposal['proposed_replacements'])==2 and proposal['requires_final_source_bound_Linux_receipt']
replacements={x['destination']:x for x in proposal['proposed_replacements']}
assert set(replacements)=={'tensor-computations/TR-04/lean/formalization.yaml','tensor-computations/TR-04/README.md'}
for path,rec in replacements.items():
    bind(REPO/path,rec['current_sha256']);bind(REPO/rec['proposed_path'],rec['proposed_sha256'])
    assert (REPO/path).read_bytes()==blob(path)

freeze=read(C/'CANONICAL_PACKAGE_PREACCEPTANCE_FREEZE_2026-10-26.json','8ee1d4585f3c0a60b101ec962fa9631ebbc043270cf35360669b8018152301eb')
before=freeze['inputs'];after=proposal['post_promotion_package_inputs']
assert len(before)==len(after)==205 and set(before)==set(after)
assert [n for n in before if before[n]!=after[n]]==['formalization.yaml']
assert after['formalization.yaml']==replacements['tensor-computations/TR-04/lean/formalization.yaml']['proposed_sha256']
for path,digest in before.items():
    bind(CANON/path,digest)
    assert hashlib.sha256(blob('tensor-computations/TR-04/lean/'+path)).hexdigest()==digest
assert sum(n.endswith('.lean') for n in after)==190
copies=read(CANON/'proof-source-lock.json')['copies']
assert len(copies)==184 and sum(x['module'].startswith('NLA.Proofs.TR04.') for x in copies)==179
for x in copies:
    assert bind(REPO/x['source'],x['source_sha256'])==bind(REPO/x['destination'],x['destination_sha256'])
    assert x['source_sha256']==x['destination_sha256']
    assert after[x['module'].replace('.','/')+'.lean']==x['source_sha256']

archive=read(DOC/'originals-before-full-proof-2026-10-26/manifest.json','81d4086ffcbc92eb2b1c92f815ed1d859f2393d0b47d2fca0c3275968d308047')
assert len(archive['records'])==25
for x in archive['records']:
    assert bind(REPO/x['original_path'],x['sha256'])==bind(REPO/x['archive_path'],x['sha256'])
    assert (REPO/x['original_path']).read_bytes()==blob(x['original_path'])
registry=read(REPO/'problem_ids.json')
assert len(registry)==217 and registry['TR-04']=='tensor-computations/TR-04/README.md'
assert (REPO/'problem_ids.json').read_bytes()==blob('problem_ids.json')
for ident,path in registry.items():
    bind(REPO/path)
    assert (REPO/path).read_bytes()==blob(path)

old_path=REPO/'tensor-computations/TR-04/README.md'
new_path=REPO/replacements['tensor-computations/TR-04/README.md']['proposed_path']
old=old_path.read_text();new=new_path.read_text()
marker='## Problem statement\n'
assert old.count(marker)==new.count(marker)==1
assert old.split(marker,1)[1]==new.split(marker,1)[1]
old_section=old.split('## Lean formalization scaffold\n',1)[1].split(marker,1)[0]
start='## Lean verification — 2026-10-26\n'
assert new.count(start)==1
new_section=new.split(start,1)[1].split(marker,1)[0]
restored=new.replace(start+new_section,'## Lean formalization scaffold\n'+old_section)
restored=restored.replace('**Status:** Lean verified  \n','**Status:** Solved  \n').replace('**Last checked:** 2026-10-26  \n','**Last checked:** 2026-09-11  \n')
assert restored==old
assert 'unfolding-rank bound' in new_section and '1000000 * Size^5' in new_section
assert 'every legal full-SVD reply trace' in new_section
for name in ['Challenge.lean','Solution.lean','SPEC.md','README.md']:
    assert sha(CANON/name)==before[name]==after[name]

sys.path.insert(0,str(REPO/'tools/lean'))
import validate_manifest as manifest
import jsonschema,yaml
old_yaml=yaml.load((CANON/'formalization.yaml').read_text(),Loader=manifest.UniqueSafeLoader)
new_yaml_path=REPO/replacements['tensor-computations/TR-04/lean/formalization.yaml']['proposed_path']
new_yaml=yaml.load(new_yaml_path.read_text(),Loader=manifest.UniqueSafeLoader)
prior_yaml=yaml.load((P/'initial-pending-wording/input-candidate/formalization.yaml').read_text(),Loader=manifest.UniqueSafeLoader)
def differences(a,b,path=()):
    if type(a)!=type(b):return [path]
    if isinstance(a,dict):
        assert set(a)==set(b)
        return [q for k in a for q in differences(a[k],b[k],path+(str(k),))]
    if isinstance(a,list):
        assert len(a)==len(b)
        return [q for k in range(len(a)) for q in differences(a[k],b[k],path+(str(k),))]
    return [] if a==b else [path]
delta=differences(old_yaml,new_yaml)
assert differences(prior_yaml,new_yaml)==[('status','comparator_result')]
assert 'final promotion receipt pending; it will be retained outside this package' in new_yaml['status']['comparator_result']
assert (P/'initial-pending-wording/input-candidate/problem-README.md').read_bytes()==new_path.read_bytes()
expected={('project','description'),('sources','0','note'),('automation','notes'),
 ('status','whole_problem_verified'),('status','canonical_status'),('status','main_results','2','verification_status'),
 ('status','phase'),('status','comparator_result'),('status','authoritative_linux_result'),('review','status'),('review','notes')}
assert set(delta)==expected
assert new_yaml['status']['whole_problem_verified'] is True
assert new_yaml['status']['canonical_status']=='Lean verified'
assert new_yaml['status']['scope']==old_yaml['status']['scope']
assert new_yaml['fidelity']==old_yaml['fidelity']
schema=read(REPO/'docs/lean/schema/v0.4.schema.json')
jsonschema.validators.validator_for(schema)(schema).validate(new_yaml)
staged=B/'schema-input'
assert not staged.exists();staged.mkdir()
for name in ['comparator.json','FullSolution.lean','Solution.lean']:
    shutil.copyfile(CANON/name,staged/name);bind(staged/name)
shutil.copyfile(new_yaml_path,staged/'formalization.yaml');bind(staged/'formalization.yaml')
out=io.StringIO()
with contextlib.redirect_stdout(out):manifest.validate(staged,schema)
(B/'schema-validation.log').write_text(out.getvalue());bind(B/'schema-validation.log')
bind(REPO/'tools/lean/validate_manifest.py')

accept=read(C/'independent-full-target-review/ACCEPTANCE.json','716bf819e742b9b8d3e7060695e0a9330c4520f25e343c101da5ce416d016f1e')
terminal=read(C/'independent-full-target-review/TERMINAL_VALIDATION.json','0994e225970bfaa2413d02b25ee953e53d1f644889102dcc87c76ffc36827c0e')
assert accept['passed'] and terminal['passed'] and accept['full_TR04_Target_proved']
assert not accept['retained_original_aggregate_passed'] and not accept['raw_result_relabelled_or_rewritten']
integrity=read(C/'independent-evidence-index/result-through-full-target-v2.json','6f7b795d432b495f0949c7f6d77c02e4ab3f2f62c89cff227955e9642c918b8e')
assert integrity['passed'] and integrity['approved_scopes']==42 and integrity['shared_project_Lean_source_union']==187
linux=read(C/'independent-linux-candidate-algebra/APPROVAL.json','8fd5d17193709a4ad5a87367a751a9ac79a34cef4a6691fa0ee45853fe1546b9')
linux_result=read(C/'independent-linux-candidate-algebra/terminal-result.json','576281c8bab2560176c60fdff3b4b4e5d638150092af15b1220213d55c0db6bf')
assert linux['outcome']=='approved' and linux_result['passed'] and linux_result['check_count']==795
assert len(linux_result['checks'])==795 and all(x['passed'] for x in linux_result['checks'])
assert linux['source_head']==HEAD and linux['executed_merge']=='d9d0a8f163c2c0309e349cfbe839d53bece11643'
assert linux['actual_Linux_import_build_markers']==187 and linux['actual_Linux_proof_build_markers']==179
assert linux['unused_helpers_without_Linux_build_claim']==['Check','Identity','Reviewed.TR04']
bind(C/'linux-pr370-candidate/original-GitHub-artifact12691512992.zip',linux['original_archive_sha256'])
bind(C/'linux-pr370-candidate/job121862750146.log',linux['original_raw_job_sha256'])
bind(C/'independent-linux-candidate-algebra/audit-linux.py',linux['auditor_sha256'])

links=[]
for source,base in [(new_path,old_path.parent),(DOC/'README.md',DOC),(DOC/'LINUX_CI_RECEIPT.md',DOC)]:
    text=source.read_text();bind(source)
    for match in re.finditer(r'\[[^\]]*\]\(([^)]+)\)',text):
        target=match.group(1).strip('<>')
        if re.match(r'^[a-zA-Z][a-zA-Z0-9+.-]*:',target) or target.startswith('#'):continue
        target=target.split('#',1)[0]
        dest=(base/target).resolve()
        assert dest.is_relative_to(REPO) and dest.exists(),str(dest)
        if dest.is_file():bind(dest)
        links.append({'source':str(source.relative_to(REPO)),'target':target,'resolved':str(dest.relative_to(REPO))})
for source in [DOC/'README.md',DOC/'LINUX_CI_RECEIPT.md']:
    txt=source.read_text()
    assert '190' in txt and '187' in txt if source.name=='LINUX_CI_RECEIPT.md' else '190' in txt
assert 'Final descriptive promotion' in (DOC/'LINUX_CI_RECEIPT.md').read_text()
assert 'separate source-bound Linux receipt' in (DOC/'LINUX_CI_RECEIPT.md').read_text()
assert 'original\n  aggregate reported false' in (DOC/'README.md').read_text()

bind(Path(__file__))
report={'passed':True,'recorded_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/recover_verification',
 'scope':'Source-only fidelity review of the exact unapplied metadata/display proposal, preserved mathematical input bytes and adequate existing complete-proof evidence. Approval to apply these two replacements; final changed package requires a new source-bound actual Linux receipt.',
 'proof_source_authorship':[],'proof_source_changes':False,'proposal_applied_by_review':False,
 'proposal_sha256':sha(P/'PROMOTION_PROPOSAL.json'),'candidate_proof_commit':HEAD,
 'approved_replacements':proposal['proposed_replacements'],'canonical_input_count':205,
 'canonical_changed_input_paths':['formalization.yaml'],'canonical_Lean190_unchanged':True,
 'all184_shared_copies_and179proof_modules_unchanged':True,'literal_Target_and_pins_unchanged':True,
 'all25_live_original_and_archive_bytes_currently_unchanged':True,'archive_preserves25_after_display_promotion':True,
 'problem_statement_suffix_byte_exact':True,'original_README_recovered_exactly_by_reversing_only_status_date_and_scaffold_section':True,
 'all216_other_registered_problem_READMEs_unchanged':True,'all217_ID_paths_unchanged':True,
 'metadata_changed_scalar_paths':['.'.join(p) for p in delta],'metadata_scope_fidelity_main_result_types_and_standard_axioms_unchanged':True,
 'schema_and_three_selected_exports_passed':True,'local_links_checked':links,
 'linked_summary_sha256':{str(p.relative_to(REPO)):sha(p) for p in [DOC/'README.md',DOC/'LINUX_CI_RECEIPT.md']},
 'full_original_mathematical_Target_accepted_locally':True,'original_false_198_aggregate_remains_excluded':True,
 'candidate_Linux_795check_receipt_reviewed':True,'candidate_Linux_run':40405628070,'candidate_Linux_executed_merge':linux['executed_merge'],
 'candidate_Linux_actual_import_scope':187,'candidate_Linux_actual_proof_scope':179,
 'proposed_final_metadata_Linux_verified':False,'requires_new_source_bound_actual_Linux_and_original_artifact_audit':True,
 'new_Lean_Comparator_or_network_execution_by_review':False,'artifact_hashes':artifacts}
q=B/'APPROVAL.json';assert not q.exists();q.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'passed':True,'sha256':sha(q),'bound_artifacts':len(artifacts),'checked_local_links':len(links)},indent=2))
