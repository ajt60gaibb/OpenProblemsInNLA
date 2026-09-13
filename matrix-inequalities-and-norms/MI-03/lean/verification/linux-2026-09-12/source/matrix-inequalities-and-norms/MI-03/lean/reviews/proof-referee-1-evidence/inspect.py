from pathlib import Path
import hashlib,json,os,re,subprocess,time
out=Path(__file__).resolve().parent;project=out.parents[1];context=json.loads((out/'fresh-environment.json').read_text());env=os.environ.copy();env['LEAN_PATH']=context['LEAN_PATH'];prefix=Path(context['prefix']);assert json.loads((out/'fresh-result.json').read_text())['result']=='PASS'
cmd=[context['lean'],'-o',str(prefix/'IndependentRefereeInspect.olean'),str(out.relative_to(project)/'Inspect.lean')];start=time.monotonic();r=subprocess.run(cmd,cwd=project,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(out/'inspection.log').write_bytes(r.stdout)
record={'command':cmd,'exit_code':r.returncode,'elapsed_seconds':round(time.monotonic()-start,3),'log_sha256':hashlib.sha256(r.stdout).hexdigest(),'source_sha256':hashlib.sha256((out/'Inspect.lean').read_bytes()).hexdigest()};(out/'inspection-result.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record));assert r.returncode==0,r.stdout.decode()
text=r.stdout.decode();assert 'warning:' not in text and 'error:' not in text
records=re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]",text);assert len(records)==12
for name,raw in records:assert [v.strip() for v in raw.split(',')]==['propext','Classical.choice','Quot.sound'],name
traversed=int(re.search(r'SAFE_PROJECT_DECLARATIONS_TRAVERSED (\d+)',text).group(1));required=re.findall(r'^REQUIRED_DEPENDENCY_PRESENT (.+)$',text,re.M)
assert len(required)==35
(out/'inspection-summary.json').write_text(json.dumps({'result':'PASS','safe_project_declarations':traversed,'actual_required_dependencies':required,'public_theorem_kinds':8,'additional_independent_kernel_axiom_reports':len(records)},indent=2)+'\n');print('PASS',traversed,'safe project declarations,',len(required),'required dependencies,',len(records),'independent kernel assertions')
