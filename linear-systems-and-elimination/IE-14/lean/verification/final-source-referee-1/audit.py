from pathlib import Path
import hashlib,json,re,subprocess,sys
import yaml
repo=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else next(p for p in Path(__file__).resolve().parents if (p/'problem_ids.json').is_file())
s=Path(__file__).parent
rel='linear-systems-and-elimination/IE-14/lean';p=repo/rel
commit='c04371f6005220866f4f069809002d319554e039';base='d8c38a795876b132c90df8d1be8682d3dcde394c';boundary='58b516b6dbb7fa4e885b679d261bf779c263aad4'
sha=lambda b:hashlib.sha256(b).hexdigest()
file_sha=lambda f:sha(f.read_bytes())
load=lambda f:json.loads(f.read_text())
git=lambda *args:subprocess.check_output(['git','-C',str(repo),*args])
checks=[]
def ck(name,ok):assert ok,name;checks.append(name)
seal=p/'reviews/final-source-inputs.json';final=load(seal)['input_sha256'];freeze=load(p/'reviews/statement-freeze.json')
ck('authoritative exact candidate seal',file_sha(seal)=='eba95af5ab465c97c346eecd5b5427ecb72c16a80d549fe85b1af799c566b54b')
ck('23 final inputs and 10 frozen inputs',len(final)==23 and len(freeze['input_sha256'])==10)
ck('candidate is immediate child of approved boundary',git('show','--no-patch','--format=%P',commit).decode().strip()==boundary)
for name,h in final.items():
 ck('candidate/current file '+name,file_sha(p/name)==sha(git('show',commit+':'+rel+'/'+name))==h)
 if (s/name).is_file():ck('actual reviewer copy '+name,file_sha(s/name)==h)
snapshot=load(s/'snapshot-inputs.json')
for name,h in snapshot.items():ck('reviewer compiled/context snapshot matches commit '+name,sha(git('show',commit+':'+rel+'/'+name))==file_sha(p/name)==h)
for name,h in freeze['input_sha256'].items():ck('frozen preproof input '+name,file_sha(p/name)==sha(git('show',boundary+':'+rel+'/'+name))==h)
for name,h in freeze['independent_statement_reports'].items():ck('prior independent approval exact '+name,file_sha(p/name)==h)
source=load(p/'reviews/initial/source-hashes.json')['files'];context={}
for name,value in source.items():
 ck('full original published source '+name,file_sha(repo/name)==sha(git('show',base+':'+name))==value['sha256'] and (repo/name).stat().st_size==value['bytes']);context[name]=value['sha256']
for name in ['problem_ids.json','docs/lean/REVIEW.md','linear-systems-and-elimination/IE-05/lean/NLA/IE05/GEPP.lean','linear-systems-and-elimination/IE-05/lean/NLA/IE05/LUTrajectory.lean']:
 ck('published registry/protocol/reuse source unchanged '+name,(repo/name).read_bytes()==git('show',base+':'+name));context[name]=file_sha(repo/name)
ck('all existing verifications and canonical pages unchanged',all(f.startswith(rel+'/') for f in git('diff','--name-only',base,commit).decode().splitlines()))
registry=load(repo/'problem_ids.json');ck('217 permanent IDs retained',len(registry)==217 and registry['IE-14']=='linear-systems-and-elimination/IE-14/README.md')
ck('canonical remains Solved','**Status:** Solved' in (p.parent/'README.md').read_text())
manifest=load(p/'lake-manifest.json');dep_revisions={}
for package in manifest['packages']:
 dep=p/'.lake/packages'/package['name'];actual=subprocess.check_output(['git','-C',str(dep),'rev-parse','HEAD'],text=True).strip()
 ck('pinned actual dependency '+package['name'],actual==package['rev']);dep_revisions[package['name']]=actual
 ck('no modified tracked dependency sources '+package['name'],not subprocess.check_output(['git','-C',str(dep),'diff','--name-only','HEAD','--','*.lean','lakefile.toml','lakefile.lean','lake-manifest.json']).strip())
ck('actual pinned compiler','Lean (version 4.33.1, arm64-apple-darwin24.6.0, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in (s/'lean-version.log').read_text())
challenge=(s/'referee-challenge-build.log').read_text();solution=(s/'referee-solution-build.log').read_text();audit=(s/'full-audit.log').read_text()
ck('fresh Challenge completed 3008 jobs','Build completed successfully (3008 jobs).' in challenge and challenge.count('declaration uses `sorry`')==7)
ck('fresh Solution completed 3642 jobs zero warnings','Build completed successfully (3642 jobs).' in solution and 'warning:' not in solution and 'error:' not in solution)
for name in final:
 if name.startswith('NLA/') and name.endswith('.lean'):
  module=name[:-5].replace('/','.')
  ck('each actual module built '+module,'Built '+module+' (' in challenge+solution)
  text=(p/name).read_text()
  ck('no holes/native/custom axioms '+name,not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b|^\s*(axiom|opaque|unsafe|partial)\b',text,re.M))
  for imp in re.findall(r'^import (.+)',text,re.M):ck('permitted import '+imp,imp.startswith(('Mathlib.','LeanCert.','NLA.IE14.')))
ck('Solution imports proof only',(p/'Solution.lean').read_text()=='import NLA.IE14.Proof\n')
ck('seven actual elaborated types identical',(s/'challenge-types.log').read_bytes()==(s/'solution-types.log').read_bytes() and (s/'challenge-types.log').read_text().count('EXACT_TYPE NLA.IE14.')==7)
closures=dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit));decls=load(s/'audit-declarations.json')
ck('all 98 source theorem closures kernel asserted',len(decls)==len(closures)==98 and set(decls)==set(closures) and 'error:' not in audit)
for name,axioms in closures.items():ck('permitted transitive closure '+name,{x.strip() for x in axioms.split(',')}<={'propext','Classical.choice','Quot.sound'})
config=load(p/'comparator.json')
ck('seven Comparator exports no definition holes',len(config['theorem_names'])==7 and config['definition_names']==[])
for name in config['theorem_names']:ck('public axiom set '+name,set(x.strip() for x in closures[name].split(','))==set(config['permitted_axioms']))
dependencies=dict(re.findall(r'ACTUAL_CERTIFICATE_DEPENDENCY ([^:]+): (\d+) project constants',audit))
for name in ['half_complex_ne_zero','norm_half_complex_le_one','witness_data','witness_attainment','canonical_result']:ck('actual certificate dependency '+name,'NLA.IE14.'+name in dependencies)
ck('explicit two kernel interval calls',(p/'NLA/IE14/Certificates.lean').read_text().count('interval_decide (trust := kernel)')==2)
ck('metadata validates seven exports','PASS (7 declarations)' in (s/'metadata-validation.log').read_text())
y=yaml.safe_load((p/'formalization.yaml').read_text())
ck('metadata exact public exports',[d['declaration'] for d in y['status']['main_results']]==config['theorem_names'])
ck('metadata legitimate zero proof holes',y['status']['sorry_count']==0 and y['status']['sorry_in_definitions']==0)
ck('metadata permitted axioms',set(y['status']['axioms'])==set(config['permitted_axioms']))
ck('requested author and affiliation',y['project']['authors']==['George Stepaniants'] and y['project']['affiliations']['George Stepaniants']=='Department of Computing and Mathematical Sciences, California Institute of Technology')
for name in ['README.md','formalization.yaml']:
 text=(p/name).read_text();ck('truthful candidate stage '+name,'pending' in text and 'Solved' in text)
 ck('Colbrook credited '+name,'Matthew J. Colbrook' in text and 'University of Cambridge' in text)
 ck('no new contact email '+name,not re.search(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',text))
for link in re.findall(r'\]\(([^)]+)\)',(p/'README.md').read_text()):
 if not re.match(r'[a-z]+:',link):ck('README link '+link,(p/link).exists())
ck('replayed contributor 27 exact results byte-identical',(s/'replayed-exact-results.json').read_bytes()==(p/'reviews/initial/exact-results.json').read_bytes())
ck('replayed source hash record byte-identical',(s/'replayed-source-hashes.json').read_bytes()==(p/'reviews/initial/source-hashes.json').read_bytes())
num=load(s/'independent-exact.json');ck('independent exact complete column diagnostics',num['checks_count']==10878 and num['front_states']==1059 and num['admissible_tie_edges']==979)
pack=p/'verification/upper-bound-contributor';pack_hashes={}
for line in (pack/'SHA256SUMS').read_text().splitlines():
 h,name=line.split(None,1);name=name.lstrip('*');ck('retained contributor evidence '+name,file_sha(pack/name)==h);pack_hashes[name]=h
for line in (pack/'original-SHA256SUMS').read_text().splitlines():
 h,name=line.split(None,1);name=name.lstrip('*');mapped=name+'.json' if name.endswith('.trace') else name
 ck('original contributor payload preserved '+name,(sha((pack/mapped).read_text().split('\nPackaging note:',1)[0].encode()) if name=='README.md' else file_sha(pack/mapped))==h)
for module in ['Front','FrontBounds','ColumnBounds']:ck('retained contributor source equals candidate '+module,(pack/'source/NLA/IE14'/f'{module}.lean').read_bytes()==(p/'NLA/IE14'/f'{module}.lean').read_bytes())
record={'result':'PASS complete source/kernel review; authoritative Linux and Comparator still pending','reviewer':'OpenAI GPT-6 Codex /root/reference_api_review independent non-implementer','candidate_commit':commit,'published_base':base,'statement_freeze_commit':boundary,'candidate_seal_sha256':file_sha(seal),'input_sha256':final,'frozen_input_sha256':freeze['input_sha256'],'source_context_sha256':context,'dependency_revisions':dep_revisions,'full_source_module_count':12,'elaborated_type_count':7,'elaborated_types_sha256':file_sha(s/'solution-types.log'),'axiom_closures':closures,'actual_certificate_project_closure_sizes':dependencies,'independent_diagnostics':{k:v for k,v in num.items() if k!='checks'},'prior_cleanup_compilation_failure':'Resolved by current Factors/Tail/WitnessEntries coercion reductions; fresh complete build succeeds without warnings. Historical preliminary record retained separately.','contributor_evidence_sha256':pack_hashes,'checks_count':len(checks),'checks':checks,'limits':'No actual Linux/Comparator run claimed; independent macOS fresh-source project build using exact existing dependency cache.'}
(s/'audit.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'result':record['result'],'checks_count':len(checks),'candidate':commit,'types':7,'axiom_closures':98,'finite_exact_checks':10878},indent=2))
