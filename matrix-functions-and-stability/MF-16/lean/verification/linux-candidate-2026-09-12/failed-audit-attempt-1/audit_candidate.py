"""Independent MF16 packaging audit adapted from the sealed IS03 structure.
No Lean, dependency, cache, network, or Git mutation command is run."""
from pathlib import Path
import datetime,hashlib,importlib.util,json,os,re,subprocess,yaml
E=Path(__file__).resolve().parent;P=E.parents[1];W=P.parents[2]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
git=lambda *args:subprocess.check_output(['git',*args],cwd=W)
baseline=json.loads((E/'baseline.json').read_text())
assert baseline['input_count']==len(baseline['reviewer_entry_inputs'])==271
assert baseline['base']=='5830ed4fb06da0659414a3deb2a40ad327aca052'
correction=json.loads((E/'wrapper-spacing-correction.json').read_text())
assert correction['before_sha256']=='952fd96bc7f800de0414e361c1739e004f5a233d99be198ed79857d9c514141a'
assert correction['after_sha256']=='8ad758f3b8e78c5fccebb5fad1e606cf8da9fb0641924a4eafe5f2406001c3d2'
assert sha(E/'formalization.initial.yaml')==correction['before_sha256']
assert sha(P/'formalization.yaml')==correction['after_sha256']
for name,r in baseline['reviewer_entry_inputs'].items():
 p=E/'formalization.initial.yaml' if name=='formalization.yaml' else P/name
 assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],name
old=yaml.safe_load((E/'formalization.initial.yaml').read_text())
metadata=yaml.safe_load((P/'formalization.yaml').read_text())
notes=old['review']['notes']
for a,b in correction['replacements'].items():notes=notes.replace(a,b)
old['review']['notes']=notes
assert old==metadata
receipt=json.loads((P/'verification/candidate-wrapper-preparation.json').read_text())
assert sha(P/'verification/candidate-wrapper-preparation.json')==baseline['wrapper_preparation_sha256']
assert receipt['preparation_author']=='/root'
assert receipt['live_wrappers']['formalization.yaml']==correction['before_sha256']
assert sha(P/'README.md')==receipt['live_wrappers']['README.md']=='c918adbb893f7afac530fa1b9582416fa7e26f1e51f12761c63bc318ca303d69'
assert sha(P/'verification/final-review-acceptance.json')==baseline['final_review_acceptance_sha256']=='94a681f53089ea8b45e9fc8e1760d015d00cfcd18af145a61c87c021aa021753'
proof=json.loads((P/'verification/proof-freeze.json').read_text())
statement=json.loads((P/'reviews/statement-freeze.json').read_text())
assert sha(P/'verification/proof-freeze.json')=='f4b21be066d0e55e56aae5b3fd1119433ef09d7ed5822d57dacab906b38ac720'
assert sha(P/'reviews/statement-freeze.json')=='eaba8311f143727f2061f2b4c945e403e62b7e9041712d983ef56ccf2e7f0587'
assert len(proof['files'])==182 and len(statement['files'])==45
archive=P/'verification/pre-candidate-README.md'
assert sha(archive)==proof['files']['README.md']==statement['files']['README.md']=='68a309b2cfd6f65dbd28d91e8b378c39928023b32a456ead4aaeb6a79a69659e'
for fz in [proof,statement]:
 for name,h in fz['files'].items():
  p=archive if name=='README.md' else P/name
  assert sha(p)==h,name
assert 'formalization.yaml' not in proof['files'] and 'formalization.yaml' not in statement['files']
assert len(proof['source_files'])==14
originals={}
for name,h in proof['source_files'].items():
 raw=git('show',proof['base']+':'+name)
 assert hashlib.sha256(raw).hexdigest()==sha(W/name)==h,name
 g=git('rev-parse',proof['base']+':'+name).decode().strip()
 assert g==proof['source_git_blobs'][name]
 originals[name]={'sha256':h,'bytes':len(raw),'git_blob':g}
nested={}
for name in baseline['reviewer_entry_inputs']:
 if Path(name).name!='EVIDENCE-MANIFEST.json':continue
 p=P/name;m=json.loads(p.read_text());expected=set()
 for rel,r in m['files'].items():
  target=(p.parent/rel).resolve()
  assert target.is_relative_to(P) and not target.is_symlink(),rel
  h=r['sha256'] if isinstance(r,dict) else r
  assert sha(target)==h,(name,rel)
  if isinstance(r,dict) and 'bytes' in r:assert target.stat().st_size==r['bytes']
  if not rel.startswith('../'):expected.add(rel)
 actual={str(f.relative_to(p.parent)) for f in p.parent.rglob('*') if f.is_file() and f!=p}
 assert actual==expected,(name,actual-expected,expected-actual)
 if 'file_count' in m:assert m['file_count']==len(m['files'])
 nested[name]={'sha256':sha(p),'bound_files':len(m['files']),'complete_inventory':True}
assert len(nested)==5,len(nested)
gate=json.loads((P/'verification/final-review-acceptance.json').read_text())
assert [r['report'] for r in gate['reports']]==['reviews/final-referee-1.md','reviews/proof-referee-2.md']
for r in gate['reports']:
 assert sha(P/r['report'])==r['sha256']
 assert sha(P/r['complete_evidence_manifest'])==r['evidence_sha256']
 assert nested[r['complete_evidence_manifest']]['bound_files']==r['bound_files']
 assert sha(P/r['fresh_result'])==r['fresh_result_sha256']
 assert r['successful_direct_source_commands']==10 and r['exact_standard_three_reports']==26
 assert r['mathematical_revision_requested'] is False
def headers(p):
 s=p.read_text()
 return {m.group(1):' '.join(s[m.end():s.index(':=',m.end())].split())
 for m in re.finditer(r'^theorem\s+(\w+)\s+',s,re.M)}
assert headers(P/'Challenge.lean')==headers(P/'Solution.lean')
names=['NLA.MF16.'+n for n in headers(P/'Challenge.lean')]
assert len(names)==9
config=json.loads((P/'comparator.json').read_text())
axioms=['propext','Classical.choice','Quot.sound']
assert config['theorem_names']==names and config['definition_names']==[] and config['permitted_axioms']==axioms
assert metadata['version']=='v0.4'
assert [r['declaration'] for r in metadata['status']['main_results']]==names
assert [r['declaration'] for r in metadata['alignment']]==names
assert metadata['status']['sorry_count']==metadata['status']['sorry_in_definitions']==0
assert metadata['status']['axioms']==axioms
assert metadata['review']['linux_verification']['status']=='pending'
assert metadata['project']['authors']==['George Stepaniants']
assert metadata['project']['affiliations']['George Stepaniants']=='Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'
for r in metadata['status']['main_results']:
 assert r['file']=='Solution.lean' and r['sorry_count']==0 and r['axioms']==axioms
 assert r['comparator_config']=='comparator.json' and r['literature_dependencies']==[]
assert len(metadata['review']['statement_reports'])==2 and len(metadata['review']['proof_reports'])==2
for r in metadata['review']['statement_reports']+metadata['review']['proof_reports']:
 assert sha(P/r['file'])==r['sha256']
for name,r in metadata['review']['proof_report_evidence'].items():
 assert sha(P/name)==r['sha256'] and (P/name).stat().st_size==r['bytes']
for name in ['statement_freeze','proof_freeze','coordinator_acceptance','historical_readme']:
 r=metadata['review'][name];assert sha(P/r['file'])==r['sha256']
links=[]
for link in re.findall(r'\[[^\]]*\]\(([^)]+)\)',(P/'README.md').read_text()):
 if '://' not in link and not link.startswith('#'):
  target=(P/link.split('#',1)[0]).resolve()
  assert target.exists() and target.is_relative_to(W),link
  links.append(link)
for name in ['README.md','formalization.yaml']:
 s=(P/name).read_text()
 assert s.endswith('\n') and not any(x.rstrip()!=x for x in s.splitlines()),name
 assert not re.search(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',s),name
 assert 'George Stepaniants' in s and 'Matthew J. Colbrook' in s
email_hits=[]
for name in baseline['reviewer_entry_inputs']:
 p=P/name
 try:s=p.read_text()
 except UnicodeDecodeError:continue
 for m in re.finditer(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',s):
  if any(part in m.group(0).lower() for part in ['stepaniants','george']):
   email_hits.append({'file':name,'line':s[:m.start()].count('\n')+1})
assert not email_hits,email_hits
checks=json.loads((E/'validation-checks.json').read_text())
assert len(checks['commands'])==2
for r in checks['commands']:
 assert r['exit_code']==0 and sha(E/r['log'])==r['log_sha256']
assert 'PASS (9 declarations)' in (E/'manifest.log').read_text()
assert 'Validated 217 permanent problem IDs against origin/main' in (E/'permanent-ids.log').read_text()
assert sha(W/'docs/lean/schema/v0.4.schema.json')=='25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce'
registry=json.loads((W/'problem_ids.json').read_text())
assert len(registry)==217 and registry['MF-16']=='matrix-functions-and-stability/MF-16/README.md'
assert sha(W/'problem_ids.json')==baseline['registry_sha256']
assert (W/'problem_ids.json').read_bytes()==git('show',proof['base']+':problem_ids.json')
assert '**Status:** Solved' in (P.parent/'README.md').read_text()
assert git('rev-parse','HEAD').decode().strip()==baseline['base']
assert not git('diff','--name-only') and not git('diff','--cached','--name-only')
statics={}
for n in ['tools/lean/validate_manifest.py','tools/validate_problem_ids.py','tools/lean/projects.py','tools/lean/harness.py',
 'tools/lean/verify.sh','tools/lean/source-lock.json','tools/lean/HARNESS.md','docs/lean/schema/README.md',
 'docs/lean/schema/v0.4.schema.json','.github/workflows/lean-verification.yml','AGENTS.md']:
 assert (W/n).read_bytes()==git('show',baseline['base']+':'+n),n
 statics[n]={'sha256':sha(W/n),'bytes':(W/n).stat().st_size}
spec=importlib.util.spec_from_file_location('mf16_candidate_projects',W/'tools/lean/projects.py')
mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
detected=mod.discover(W)
project={'id':'MF-16','project':'matrix-functions-and-stability/MF-16/lean'}
assert project in detected
assert mod.select(detected,[project['project']+'/formalization.yaml'])==[project]
lock=json.loads((W/'tools/lean/source-lock.json').read_text())
assert lock['commit']=='8d1b0c0545a77b40245e84705aa7d273e6c81e62'
assert lock['lean_toolchain']==(P/'lean-toolchain').read_text().strip()
assert 'defaultTargets = ["Challenge"]' in (P/'lakefile.toml').read_text()
assert 'name = "Solution"' in (P/'lakefile.toml').read_text()
assert config['challenge_module']=='Challenge' and config['solution_module']=='Solution'
workflow=(W/'.github/workflows/lean-verification.yml').read_text()
assert 'runs-on: ubuntu-24.04' in workflow and 'tools/lean/verify.sh "$LEAN_PROJECT"' in workflow
harness=(W/'tools/lean/harness.py').read_text()
body=harness[harness.index('def verify('):harness.index('def main(')]
assert 'linux_requirements()' in body and 'run_controls(tool_dir, logdir, env)' in body
assert 'Lean default kernel accepts the solution' in body and 'Your solution is okay!' in body
out={'result':'PASS','phase':'MF-16 independent concrete Linux candidate packaging audit',
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'preparer':'/root, coordinator and disclosed route contributor',
 'independent_packaging_reviewer':'/root/mf16_final_referee',
 'reviewer_also_prior_final_mathematical_referee':True,'additional_mathematical_approvals_added':0,
 'reviewer_entry_input_count':271,'reviewer_entry_inputs_unchanged_except_spacing_only_yaml':270,
 'full_proof_inputs_preserved_with_archive_mapping':182,'other_proof_inputs_byte_identical':181,
 'full_statement_inputs_preserved_with_archive_mapping':45,'other_statement_inputs_byte_identical':44,
 'historical_archive_sha256':sha(archive),'current_README_sha256':sha(P/'README.md'),
 'current_formalization_yaml_sha256':sha(P/'formalization.yaml'),
 'metadata_spacing_correction_receipt_sha256':sha(E/'wrapper-spacing-correction.json'),
 'original_source_Git_blobs':originals,'complete_nested_evidence_inventories':nested,
 'all_nine_exports':names,'definition_exceptions':[],'permitted_axioms':axioms,
 'metadata_and_exact_coverage':'PASS; metadata consistency, not actual Comparator execution',
 'relative_README_links':links,'George_email_hits':email_hits,
 'permanent_ID_validation':'PASS 217 IDs against origin/main; all originals and tracked files unchanged',
 'repository_static_inputs':statics,'actual_changed_project_selection':'MF-16 selected from its canonical registered path',
 'unchanged_default_lake_target':'Challenge; explicit Solution is registered',
 'Ubuntu_workflow_and_real_controls':'Statically connected, runtime remains pending',
 'tracked_and_staged_diff_empty':True,'Lean_Lake_build_or_dependency_download_copy_cache_change':False,
 'canonical_status':'Solved, unchanged','actual_Linux_Comparator_default_kernel_controls':'pending',
 'commit_push_publication':False}
(E/'integrity.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'result':'PASS','proof_inputs':182,'statement_inputs':45,'original_sources':14,
 'nested_manifests':len(nested),'metadata_declarations':9,'initial_inputs_preserved':271,
 'yaml_sha256':sha(P/'formalization.yaml')}))
