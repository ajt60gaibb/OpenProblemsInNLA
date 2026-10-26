#!/usr/bin/env python3
"""Seal independently fetched final CI evidence, current inputs and context."""
from pathlib import Path
from datetime import datetime,timezone
import gzip,hashlib,json,re
B=Path(__file__).resolve().parent;REPO=B.parents[5];C=B/'collection'
HEAD='09cd782576559502787fb536bc1427bf64b7b3e4'
DRIVER='19fa3d2a8cee184f040e6349198ec29797a55cc388972c3e2230154dae90fd9b'
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
result=read(B/'terminal-result.json')
assert result['passed'] and result['error'] is None and result['check_count']==1214
assert len(result['checks'])==1214 and all(x['passed'] for x in result['checks'])
assert bind(B/'audit-linux.py',DRIVER)==result['driver_sha256']
assert result['head']==HEAD and result['run']==40408919808 and result['job']==121875088207 and result['artifact']==12692842329
assert result['base']=='01141f415715a27473cabc1f35ef898e86aafae2'
assert result['executed_merge']=='5c58fa518732636edcb21c377f8014fa00f34480'
assert (result['package_inputs'],result['Lean_inputs'],result['copied_sources'],result['proof_sources'])==(205,190,184,179)
assert len(result['actual_import_build_scope'])==len(result['actual_build_markers'])==187
assert result['input_bound_without_Linux_build_marker']==['Check','Identity','Reviewed.TR04']
assert result['expected_axioms']=={'candidate_count_le_first_mode':[],'cyclic_window_count_le_first_mode':[],'NLA.TR04.target':['propext','Classical.choice','Quot.sound']}
for path,digest in result['evidence_file_sha256'].items():bind(Path(path),digest)
assert bind(C/'original-GitHub-artifact12692842329.zip')=='bd48f52a1f448b3f09b8f39e2a07a946b38bc9e610d9ca55f965a9a80196efcc'
assert (C/'original-GitHub-artifact12692842329.zip').stat().st_size==33585
assert bind(C/'job121875088207.log')=='03be81cfc841504b92aa8a41e47d2798ba97996d9a18962779bb5b94f884f920'
raw=(C/'job121875088207.log').read_bytes();assert len(raw)==248078 and raw.startswith(b'\xef\xbb\xbf')
assert gzip.decompress((C/'job121875088207.log.gz').read_bytes())==raw
wrapper_correspondence={}
for name in ['run','jobs','artifacts']:
    wrapper=read(C/('connector-'+name+'-final.json'))
    assert not wrapper['isError']
    decoded=json.loads(wrapper['structuredContent']['content'])
    assert decoded==read(C/(name+'.json'))
    wrapper_correspondence[name]={'original_tool_wrapper':str((C/('connector-'+name+'-final.json')).relative_to(REPO)),
      'wrapper_sha256':sha(C/('connector-'+name+'-final.json')),'same_complete_JSON_value':True,
      'same_serialized_bytes_claim':False}
logwrapper=read(C/'connector-job-log-final.json')
assert not logwrapper['isError'] and logwrapper['structuredContent']['content'].encode('utf-8')==raw
run=read(C/'run.json');jobs=read(C/'jobs.json');listing=read(C/'artifacts.json');metadata=read(C/'artifact-metadata.json')
assert run['status']=='completed' and run['conclusion']=='success' and run['event']=='pull_request'
assert run['head_sha']==HEAD and run['run_attempt']==1
assert next(j for j in jobs['jobs'] if j['id']==121875088207)['conclusion']=='success'
assert next(a for a in listing['artifacts'] if a['id']==12692842329)==metadata
assert metadata['digest']=='sha256:'+result['archive_sha256']
provenance={'recorded_utc':datetime.now(timezone.utc).isoformat(),'collector':'/root/recover_verification',
 'separate_network_retrieval_from_root_copy':True,'repository':'ajt60gaibb/OpenProblemsInNLA',
 'run':40408919808,'job':121875088207,'artifact':12692842329,'fixed_source_head':HEAD,
 'API_method':'Independent GitHub connector fetch calls for terminal run, jobs and artifacts; complete original wrappers retained, parsed JSON values compared.',
 'ZIP_method':'GitHub download_workflow_artifact connector followed by system curl with verified TLS, --fail --silent --show-error --location, to a new local ZIP file.',
 'download_file_id':'file_00000000eb4481f4b33f1cef77eab106','transient_download_URL_persisted':False,
 'raw_job_method':'Independent GitHub fetch_workflow_job_logs connector; original content UTF-8 encoded exactly from retained wrapper, preserving initial BOM, Unicode and newlines.',
 'raw_job_bytes':248078,'raw_job_sha256':result['raw_log_sha256'],'ZIP_bytes':33585,'ZIP_sha256':result['archive_sha256'],
 'API_artifact_digest_and_raw_upload_digest_verified':True,'gzip_exact_raw_content':True,'gzip_mtime':0,
 'terminal_wrapper_correspondence':wrapper_correspondence,
 'initial_queued_and_in_progress_wrappers_retained_without_relabelling':True,
 'new_Lean_or_Comparator_executed_by_collector':False,'signed_URL_or_authentication_material_in_provenance':False}
p=C/'COLLECTION_PROVENANCE.json';assert not p.exists();p.write_text(json.dumps(provenance,indent=2)+'\n');bind(p)

display=read(B/'POSTPROMOTION_DISPLAY.json','c516d96ea9bb1b5c1f339f28436c2ac91700a69af1b6d42f7136da1ecb0eb6cf')
assert display['passed'] and display['exact_source_head']==HEAD
assert display['all217_ID_path_pairs_unchanged'] and display['all216_other_problem_pages_byte_exact']
assert display['all13_catalog_outputs_reproduced_in_memory_byte_exact'] and display['required_ID_tests_passed']
assert display['status_counts']['Lean verified']==87 and display['status_counts']['Solved']==31
for path,digest in display['artifact_hashes'].items():bind(REPO/path,digest)
historical=read(B/'HISTORICAL_CHECKPOINT.json','c9f6f2ff37388b71efbe0e77fe78c84ae6bf60fcad3c718171d24923935c256a')
assert historical['passed'] and historical['all6349_historical_bytes_preserved_in_checkpoint']
assert historical['original_false_aggregate_preserved'] and historical['separate_terminal_validation_preserved']
assert historical['checkpoint']=='e7b6c9c592d823973aac5d39a6dbe6c81c0005ce'
freeze_path=B.parent/'CANONICAL_PROMOTION_FREEZE_2026-10-26.json'
freeze=read(freeze_path,'44b5df77ea7ed70c35aac6e87b2001f2b6860a36f58f1156a50d01a3c83374f7')
for name,digest in freeze['inputs'].items():bind(REPO/freeze['project']/name,digest)
source_review=B.parent/'independent-full-target-review/ACCEPTANCE.json'
read(source_review,'716bf819e742b9b8d3e7060695e0a9330c4520f25e343c101da5ce416d016f1e')
promotion_review=B.parent/'independent-promotion-review/APPROVAL.json'
read(promotion_review,'8c17dfa96dea9c4e6c36b196678bc59de9073d622bd9edbee6fa7c544a9e66c8')
candidate_review=B.parent/'independent-linux-candidate-algebra/APPROVAL.json'
read(candidate_review,'8fd5d17193709a4ad5a87367a751a9ac79a34cef4a6691fa0ee45853fe1546b9')
read(B.parent/'independent-linux-promotion-algebra/VERIFIER_AUDITOR_SOURCE_REVIEW.json','90a349ab9f29935dd15c2fed4431361df7e84f5363523e8dff44895d78b24f42')
for p in sorted(B.rglob('*')):
    if not p.is_file() or '__pycache__' in p.parts:continue
    assert p.suffix not in {'.olean','.ilean','.pyc'},str(p)
    bind(p)
approval={'passed':True,'outcome':'approved','recorded_utc':datetime.now(timezone.utc).isoformat(),
 'reviewer':'/root/recover_verification','proof_source_authorship':[],
 'scope':'Complete original TR04 mathematical Target previously independently source/kernel accepted; final promoted205-input package independently accepted from exact actual Linux original artifact/raw-job evidence, together with approved descriptive delta, immutable originals/IDs and postpromotion catalog binding.',
 'source_head':HEAD,'executed_merge':result['executed_merge'],'base':result['base'],
 'run':result['run'],'job':result['job'],'artifact':result['artifact'],'actual_auditor_checks':1214,
 'auditor_sha256':DRIVER,'terminal_result_sha256':sha(B/'terminal-result.json'),
 'final_promotion_freeze_sha256':sha(freeze_path),'canonical_inputs':205,'Lean_inputs':190,
 'shared_copies':184,'proof_modules':179,'actual_Linux_compiled_import_closure':187,
 'local_fresh_audits_cover_unused_Linux_helpers':['Check','Identity','Reviewed.TR04'],
 'selected_export_axioms':result['expected_axioms'],'LeanCert_mode':'kernel','Comparator_profile':'default',
 'all190_Lean_inputs_identical_to_original_proof_candidate027':True,
 'only_canonical205_input_delta_from_candidate':'formalization.yaml',
 'all25_original_archive_bytes_exact':True,'all24_unmodified_live_original_bytes_exact':True,
 'changed_display_README_exact_approved_v2':True,'entire_original_problem_statement_suffix_exact':True,
 'all217_IDs_and216_other_problem_pages_unchanged':True,
 'postpromotion_display_and_catalog_binding_sha256':sha(B/'POSTPROMOTION_DISPLAY.json'),
 'historical6349_checkpoint_binding_sha256':sha(B/'HISTORICAL_CHECKPOINT.json'),
 'historical_false_aggregate_or_comparison_placeholder_accepted_as_proof':False,
 'raw_original_ZIP_sha256':result['archive_sha256'],'raw_original_job_sha256':result['raw_log_sha256'],
 'independent_network_collection':True,'collection_provenance_sha256':sha(C/'COLLECTION_PROVENANCE.json'),
 'complete_original_Target_Lean_verified':True,'final_source_bound_Linux_Comparator_accepted':True,
 'new_local_Lean_Comparator_or_Linux_execution_by_auditor':False,'proof_or_package_source_changes':False,
 'remote_PR_merge_performed_or_authorized_by_receipt':False,
 'artifact_hashes':artifacts,
 'context_note':'Candidate027 and historical pre-promotion receipts retain their own exact source context; they are not relabelled as final inputs. The separately approved metadata/display proposal is bound to final09cd and actual executed PR merge5c58. All190 mathematical Lean bytes remain identical. This receipt proves no other campaign problem and makes no external human endorsement claim.'}
q=B/'APPROVAL.json';assert not q.exists();q.write_text(json.dumps(approval,indent=2)+'\n')
seal={'receipt_path':str(q.relative_to(REPO)),'receipt_sha256':sha(q),'artifact_hashes':artifacts}
(B/'FILE_SHA256.json').write_text(json.dumps(seal,indent=2)+'\n')
print(json.dumps({'passed':True,'approval_sha256':sha(q),'terminal_result_sha256':sha(B/'terminal-result.json'),'bound_artifacts':len(artifacts),'seal_sha256':sha(B/'FILE_SHA256.json')},indent=2))
