from pathlib import Path
import datetime,hashlib,json,subprocess
E=Path(__file__).resolve().parent; P=E.parents[1];W=P.parents[2]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
manifest=E/'EVIDENCE-MANIFEST.json';assert not manifest.exists()
rows=[]
for rel in ['verification/proof-freeze.json','reviews/statement-freeze.json']:
 data=json.loads((P/rel).read_text())
 for name,h in data['files'].items():assert sha(P/name)==h,name
 for name,h in data['source_files'].items():
  b=subprocess.check_output(['git','show',data['base']+':'+name],cwd=W)
  assert hashlib.sha256(b).hexdigest()==h and b==(W/name).read_bytes(),name
 rows.append({'path':rel,'sha256':sha(P/rel),'project_files_preserved':len(data['files']),'original_Git_files_preserved':len(data['source_files'])})
record=json.loads((E/'execution.json').read_text())
assert record['verdict']=='PASS_LOCAL_SOURCE_AND_INSPECTION'
assert record['only_recorded_generated_objects_removed'] and not Path(record['prefix']).exists()
assert len(record['commands'])==18 and all(c['exit_code']==0 for c in record['commands'])
for c in record['commands']:assert sha(P/c['source'])==c['sha256'] and sha(E/c['log'])==c['log_sha256']
assert sha(E/'execution.json')=='7bd3878a17186e7323bdf1149d369a7ecdd8ea5dee8cb63e076f4c291ee92c04'
assert sha(E/'source-and-output-audit.json')=='cb68733a96e530fc05ca8849256ca023427aec68e12f50f94ef64ce4b0f3a003'
report=P/'reviews/final-referee-1.md'
(E/'final-integrity.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewer':'/root/ra09_final_referee1','verdict':'APPROVE_FROZEN_COMPLETE_MATHEMATICS','report_sha256':sha(report),'preserved_freezes':rows,'fresh_execution_sha256':sha(E/'execution.json'),'source_output_audit_sha256':sha(E/'source-and-output-audit.json'),'no_mathematical_or_metadata_edits':True,'own_generated_objects_hashed_before_removal':len(record['generated_before_cleanup']),'own_generated_bytes_removed':sum(r['bytes'] for r in record['generated_before_cleanup']),'Linux_claim':False,'second_referee_operational_and_publication_gates':'separate'},indent=2)+'\n')
files={str(q.relative_to(E)):{'sha256':sha(q),'bytes':q.stat().st_size} for q in sorted(E.rglob('*')) if q.is_file() and q!=manifest}
assert not any(q.is_symlink() for q in E.rglob('*'))
files['../final-referee-1.md']={'sha256':sha(report),'bytes':report.stat().st_size}
manifest.write_text(json.dumps({'reviewer':'/root/ra09_final_referee1','phase':'Independent final mathematical review 1','scope':'Complete referee evidence and signed-role report; all nested files included. Only this exact outer manifest is self-excluded. Frozen input integrity is separately reverified in the bound final-integrity and source-output audit.','exact_self_exclusion':'EVIDENCE-MANIFEST.json','files':dict(sorted(files.items())),'bound_file_count':len(files),'internal_file_count':len(files)-1},indent=2)+'\n')
assert set(files)-{'../final-referee-1.md'}=={str(q.relative_to(E)) for q in E.rglob('*') if q.is_file() and q!=manifest}
for name,row in files.items():assert sha(E/name)==row['sha256'] and (E/name).stat().st_size==row['bytes']
print(json.dumps({'verdict':'APPROVE','report':str(report),'report_sha256':sha(report),'evidence_manifest':str(manifest),'evidence_manifest_sha256':sha(manifest),'bound_files':len(files),'internal_files':len(files)-1,'final_integrity_sha256':sha(E/'final-integrity.json'),'fresh_execution_sha256':sha(E/'execution.json'),'mathematical_edits':False,'Lean_commands':18,'elaborated_signature_comparisons':17,'axiom_prints':66,'final_project_closure':115,'all_export_project_closure':139,'required_bridges_final':40,'required_bridges_all':49},indent=2))
