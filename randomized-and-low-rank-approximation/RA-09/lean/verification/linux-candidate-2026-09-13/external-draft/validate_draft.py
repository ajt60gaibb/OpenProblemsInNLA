"""Static validation of an external RA09 wrapper draft; no proof run or live edit."""
from pathlib import Path
import hashlib,json,re,subprocess,datetime,yaml,jsonschema
D=Path(__file__).resolve().parent
W=Path('/tmp/nla-lean-ra09-worktree');P=W/'randomized-and-low-rank-approximation/RA-09/lean'
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=W)
freeze=json.loads((P/'verification/proof-freeze.json').read_text())
assert sha(P/'verification/proof-freeze.json')=='533f5c328cdaf8c1f23f238f8c71b7b4b2fdabb2f532d58a398d4ab2434ccf7e'
for name,h in freeze['files'].items():assert sha(P/name)==h,name
for name,h in freeze['source_files'].items():
 raw=git('show',freeze['base']+':'+name)
 assert hashlib.sha256(raw).hexdigest()==h and (W/name).read_bytes()==raw,name
 assert git('rev-parse',freeze['base']+':'+name).decode().strip()==freeze['source_git_blobs'][name]
metadata=yaml.safe_load((D/'formalization.yaml').read_text());schema=W/'docs/lean/schema/v0.4.schema.json'
assert sha(schema)=='25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce'
jsonschema.Draft7Validator(json.loads(schema.read_text())).validate(metadata)
config=json.loads((P/'comparator.json').read_text());names=config['theorem_names'];axioms=config['permitted_axioms']
assert len(names)==17 and config['definition_names']==[]
assert [x['declaration'] for x in metadata['status']['main_results']]==names
assert [x['declaration'] for x in metadata['alignment']]==names
assert all(x['literature_dependencies']==[] and x['file']=='Solution.lean' and x['comparator_config']=='comparator.json'
 and x['sorry_count']==0 and x['axioms']==axioms for x in metadata['status']['main_results'])
assert metadata['status']['sorry_count']==metadata['status']['sorry_in_definitions']==0
assert metadata['status']['axioms']==axioms==['propext','Classical.choice','Quot.sound']
headers=lambda x:dict(re.findall(r'^theorem (\w+)(.*?):= by',x,re.M|re.S))
assert headers((P/'Challenge.lean').read_text())==headers((P/'Solution.lean').read_text())
assert ['NLA.RA09.'+x for x in headers((P/'Solution.lean').read_text())]==names
references=[]
for key in ['statement_freeze','proof_freeze','statement_gate']:
 r=metadata['review'][key];assert sha(P/r['file'])==r['sha256'];references.append(r)
for key in ['statement_reports','proof_reports']:
 for r in metadata['review'][key]:assert sha(P/r['file'])==r['sha256'];references.append(r)
for file,r in metadata['review']['proof_report_evidence'].items():
 assert sha(P/file)==r['sha256'] and (P/file).stat().st_size==r['bytes'];references.append({'file':file,**r})
assert metadata['review']['candidate_documents']['frozen_readme_sha256']==sha(P/'README.md')
# Reference placeholders remain deliberate; all live implementation files are unchanged and clean.
code=[P/'Solution.lean',*sorted((P/'NLA/RA09').glob('*.lean'))]
assert sum(len(re.findall(r'^#assert_trust kernel ',x.read_text(),re.M)) for x in code)==49
assert metadata['project']['authors']==['George Stepaniants']
assert metadata['project']['affiliations']['George Stepaniants']=='Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'
for file in ['README.md','formalization.yaml']:
 assert not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}',(D/file).read_text())
 assert 'Matthew J. Colbrook' in (D/file).read_text()
assert metadata['review']['coordinator_acceptance']['status']=='pending'
assert metadata['review']['linux_verification']['status']=='pending'
assert not (P/'formalization.yaml').exists()
assert sha(P/'README.md')=='ca0cd8e9da1abf5e929a528e98a67b13143056ad1b9403c6477093a1d68fbd0c'
links=[]
for link in re.findall(r'\]\(([^)]+)\)',(D/'README.md').read_text()):
 if not link.startswith(('http:','https:')):
  target=(D/link) if link=='formalization.yaml' else (P/link)
  assert target.exists(),link
  links.append(link)
registry=(W/'problem_ids.json').read_bytes();assert registry==git('show',freeze['base']+':problem_ids.json')
assert json.loads(registry)['RA-09']=='randomized-and-low-rank-approximation/RA-09/README.md'
assert '**Status:** Solved' in (P.parent/'README.md').read_text()
assert not git('diff','--','randomized-and-low-rank-approximation/RA-09','problem_ids.json')
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verdict':'PASS static external draft checks',
 'preparer':'/root/mf16_final_referee','role':'Previously independent RA09 final mathematical referee 2; now document preparer, no extra independent approval',
 'external_only':True,'project_root':str(P),'schema_sha256':sha(schema),'metadata_version':'v0.4',
 'metadata_exports':names,'alignment_count':len(metadata['alignment']),'exact_Challenge_Solution_textual_contracts':True,
 'no_literature_assumption_or_definition_exception':True,'actual_embedded_source_kernel_assertions':49,
 'proof_freeze_sha256':sha(P/'verification/proof-freeze.json'),'frozen_project_files_preserved':361,'original_Git_source_files_preserved':17,
 'review_references':references,'local_links_as_installed':links,
 'root_acceptance_file_currently_exists':(P/'verification/final-review-acceptance.json').exists(),
 'live_wrappers_unchanged':True,'canonical_status':'Solved, unchanged','permanent_registry_count':len(json.loads(registry)),
 'no_proof_run_or_cache_copy_download':True,'no_Git_status_or_publication_change':True,
 'draft_files':{name:{'sha256':sha(D/name),'bytes':(D/name).stat().st_size} for name in ['README.md','formalization.yaml']},
 'status_updates_required_before_live_installation':['Root must accept both final reviews and supply exact acceptance hash; replace draft pending-coordinator status with that accepted fact.',
 'Archive the exact frozen historical README before replacing it; record exact before/after wrappers and source-freeze mapping.',
 'Change external-only installation prose to actual candidate-preparation facts after authorized live installation.',
 'Keep authoritative Ubuntu/default-kernel/Comparator/control, operational and publication gates pending until each actually passes.',
 'Independent candidate packager must review the concrete wrappers and complete input inventory; this preparer does not supply that additional approval.']}
(D/'draft-checks.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'verdict':'PASS','exports':17,'frozen_inputs':361,'original_sources':17,'draft_files':record['draft_files']}))
