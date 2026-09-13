"""Independent IS-03 referee 2: fresh statement sources, no theorem implementation."""
from pathlib import Path
import datetime, hashlib, json, os, platform, re, subprocess, tempfile, time

out=Path(__file__).resolve().parent
project=out.parents[1]
repo=project.parents[2]
cache=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean')
toolchain=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
git=lambda p,*a:subprocess.check_output(['git','-C',str(p),*a])
write=lambda name,obj:(out/name).write_text(json.dumps(obj,indent=2)+'\n')
freeze_path=project/'reviews/statement-freeze.json'
assert sha(freeze_path)=='588196a54decb127a814dc4860621505d6874a077295f3e30a782d7f28b8ac6c'
assert sha(project/'reviews/statement-handoff.md')=='3c1d998ba3d3a658a7d9ea706e4357ab3587757050cef70e6f366481affd7c68'
freeze=json.loads(freeze_path.read_text())
assert len(freeze['files'])==34 and len(freeze['source_files'])==10
def frozen_check():
    assert not (project/'Solution.lean').exists() and not (project/'NLA/IS03/Proof.lean').exists()
    for name,record in freeze['files'].items():
        h=record['sha256'] if isinstance(record,dict) else record
        assert sha(project/name)==h,name
        if isinstance(record,dict):assert (project/name).stat().st_size==record['bytes'],name
    for name,h in freeze['source_files'].items():
        assert sha(repo/name)==h,name
        assert (repo/name).read_bytes()==git(repo,'show',freeze['base']+':'+name),name
frozen_check();write('integrity-before.json',freeze)
manifest=json.loads((project/'lake-manifest.json').read_text());pins=[]
for pkg in manifest['packages']:
    p=cache/'.lake/packages'/pkg['name']
    rev=git(p,'rev-parse','HEAD').decode().strip();status=git(p,'status','--porcelain=v1').decode()
    assert rev==pkg['rev'] and not status,(pkg['name'],rev,status)
    pins.append({'name':pkg['name'],'revision':rev,'path':str(p.resolve()),'source_clean':True,'object_directory_present':(p/'.lake/build/lib/lean').is_dir()})
assert len(pins)==10;write('dependency-pins.json',pins)
prefix=Path(tempfile.mkdtemp(prefix='nla-is03-statements-ref2-',dir='/tmp'))
order=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib','leancert']
paths=[prefix,*((cache/'.lake/packages'/name/'.lake/build/lib/lean').resolve() for name in order),toolchain/'lib/lean']
assert all(p==prefix or '/.lake/packages/' in str(p) or p==toolchain/'lib/lean' for p in paths)
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,paths));lean=str(toolchain/'bin/lean')
version=subprocess.check_output([lean,'--version'],text=True).strip();assert '4.33.1' in version
write('environment.json',{'scope':'Independent local macOS statement-only source elaboration. Matching MI-22 dependency objects reused read-only; no Lake/dependency build/Linux Comparator.',
 'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'platform':platform.platform(),'lean':lean,'lean_version':version,
 'fresh_prefix':str(prefix),'LEAN_PATH':env['LEAN_PATH'],'excluded_old_project_object_directories':[str(project/'.lake/build/lib/lean'),str(cache/'.lake/build/lib/lean')]})
commands=[]
for source in ['NLA/IS03/Definitions.lean','Challenge.lean','reviews/statement-referee-2-evidence/Inspect.lean']:
    target=prefix/(Path(source).with_suffix('.olean') if not source.startswith('reviews/') else Path('IndependentInspect.olean'))
    target.parent.mkdir(parents=True,exist_ok=True)
    cmd=[lean,'-o',str(target),source];start=time.monotonic()
    r=subprocess.run(cmd,cwd=project,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=out/(Path(source).stem+'.log');log.write_bytes(r.stdout)
    commands.append({'source':source,'command':cmd,'exit_code':r.returncode,'seconds':round(time.monotonic()-start,3),
                     'source_sha256':sha(project/source),'object_sha256':sha(target) if target.exists() else None,'log_sha256':sha(log)})
    write('fresh-checks.json',commands);print(source,r.returncode,flush=True)
    assert r.returncode==0,r.stdout.decode()
    text=r.stdout.decode();assert 'error:' not in text
    if source=='Challenge.lean':assert text.count('declaration uses `sorry`')==7 and text.count('warning:')==7
    else:assert 'warning:' not in text,text
frozen_check()
raw=(out/'Inspect.log').read_text()
rows=[]
for name,body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw):
    axioms={re.sub(r'\.\{.*?\}','',x.strip()) for x in body.split(',') if x.strip()}
    rows.append({'declaration':name,'axioms':sorted(axioms)})
definition_names=['RealMatrix','EntrywiseNonnegative','normalizedDerivative','DerivativeRealizabilityConjecture','witnessMatrix','witnessPolynomial','derivativePolynomial','traceMoments']
for name in definition_names:
    target='NLA.IS03.'+name
    rows_for_target=[r for r in rows if r['declaration']==target]
    if not rows_for_target:
        assert "'"+target+"' does not depend on any axioms" in raw,target
        rows.append({'declaration':target,'axioms':[]})
    else:
        assert len(rows_for_target)==1 and set(rows_for_target[0]['axioms'])<={'propext','Classical.choice','Quot.sound'},target
for name in ['NLA.IS03.trace_moment_certificate','NLA.IS03.not_derivativeRealizabilityConjecture']:
    r=[r for r in rows if r['declaration']==name];assert len(r)==1 and 'sorryAx' in r[0]['axioms'],name
write('axioms.json',{'definition_kernel_assertions':8,'definition_axioms_allowed_only_standard3_or_subset':True,
 'admitted_Challenge_reports_are_explicitly_not_proofs':True,'rows':rows})
write('fresh-result.json',{'result':'PASS','fresh_command_count':len(commands),'definition_only_kernel_assertions':8,'intentional_Challenge_holes':7,
 'statement_freeze_preserved':True,'original_sources_preserved':True,'scope':'Statement typechecking and definition trust only. No target proved, no scalar certificate executed, no Linux check.'})
print('PASS: 3 independent fresh statement commands; 8 definition-only kernel audits; 7 intentional Challenge holes',flush=True)
