"""Independent root statement-review elaboration, adapted from the campaign driver.
No proof implementation or independent/Linux verification is claimed.
The optional dependency root permits a read-only reuse of an existing private
campaign cache while the host disk is full; it never imports old project objects.
"""
from pathlib import Path
import datetime,hashlib,json,os,platform,re,subprocess,tempfile,time

PROJECT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent
BIN=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin')
DEFAULT=PROJECT/'.lake/packages'
PACKAGES=Path(os.environ.get('NLA_IE23_DEPENDENCY_ROOT',str(DEFAULT)))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not (PROJECT/'Solution.lean').exists()
assert not (PROJECT/'NLA/IE23/Proof.lean').exists()
boundary=['NLA/IE23/Definitions.lean','Challenge.lean','NUMERICAL_TARGETS.md',
          'SOURCE_CORRESPONDENCE.md','lakefile.toml','lake-manifest.json','lean-toolchain']
before={x:sha(PROJECT/x) for x in boundary}
pins=[]
for package in json.loads((PROJECT/'lake-manifest.json').read_text())['packages']:
    d=PACKAGES/package['name']
    rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=d,text=True).strip()
    dirty=subprocess.check_output(['git','status','--porcelain'],cwd=d,text=True)
    assert rev==package['rev'] and not dirty,(package['name'],rev,dirty)
    pins.append({'name':package['name'],'path':str(d),'expected':package['rev'],
                 'actual':rev,'git_status_porcelain':dirty})
assert len(pins)==10
(OUT/'dependency-pins.json').write_text(json.dumps(pins,indent=2)+'\n')

(PROJECT/'.verification').mkdir(exist_ok=True)
prefix=Path(tempfile.mkdtemp(prefix='ie23-referee2-statements-',dir=PROJECT/'.verification'))
paths=[str(prefix)]+[str(PACKAGES/p['name']/'.lake/build/lib/lean') for p in reversed(pins)]
paths.append(str(BIN.parent/'lib/lean'))
# Only a new prefix, the pinned dependencies, and the exact Lean toolchain.
# No previous project or referee compilation prefix is retained.
env=dict(os.environ,LEAN_PATH=os.pathsep.join(paths))
record={'status':'RUNNING','date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'platform':platform.platform(),'independent_review':True,'Linux_Comparator':False,
        'lean_version':subprocess.check_output([str(BIN/'lean'),'--version'],text=True).strip(),
        'dependency_root':str(PACKAGES),'dependency_objects_reused':True,
        'own_project_dependencies':PACKAGES.resolve()==DEFAULT.resolve(),
        'old_project_objects_excluded':True,'LEAN_PATH':env['LEAN_PATH'],
        'fresh_prefix':str(prefix),'boundary_before':before,'commands':[]}
for label,relative,holes in [('definitions','NLA/IE23/Definitions.lean',0),
                             ('challenge','Challenge.lean',8),
                             ('inspection','reviews/statement-referee-2-root-evidence/Inspect.lean',0)]:
    argv=[str(BIN/'lean')]
    if label!='inspection':
        output=prefix/Path(relative).with_suffix('.olean')
        output.parent.mkdir(parents=True,exist_ok=True)
        argv += ['-o',str(output)]
    argv.append(relative)
    print('Checking',relative,flush=True)
    start=time.monotonic()
    cp=subprocess.run(argv,cwd=PROJECT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=OUT/f'fresh-{label}.log';log.write_bytes(cp.stdout)
    record['commands'].append({'source':relative,'source_sha256':sha(PROJECT/relative),
      'command':argv,'exit_code':cp.returncode,'elapsed_seconds':time.monotonic()-start,
      'log':log.name,'log_sha256':sha(log)})
    (OUT/'fresh-checks.json').write_text(json.dumps(record,indent=2)+'\n')
    print('Exit',cp.returncode,flush=True)
    assert cp.returncode==0,cp.stdout.decode()
    assert cp.stdout.count(b'declaration uses `sorry`')==holes,cp.stdout.decode()
    assert cp.stdout.count(b'warning:')==holes,cp.stdout.decode()
    assert b'error:' not in cp.stdout
record['boundary_after']={x:sha(PROJECT/x) for x in boundary}
assert before==record['boundary_after']
axioms=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",
                   (OUT/'fresh-inspection.log').read_text())
declarations=re.findall(r'^(?:abbrev|def)\s+(\w+)',
                         (PROJECT/'NLA/IE23/Definitions.lean').read_text(),re.M)
assert len(axioms)==len(declarations),(len(axioms),len(declarations))
for name,raw in axioms:
    assert {x.strip() for x in raw.split(',') if x.strip()}<= {'propext','Classical.choice','Quot.sound'},name
record.update(status='PASS',fresh_commands=3,definition_audits=len(axioms),
              intentional_challenge_holes=8,proof_absent=True)
(OUT/'definition-axioms.json').write_text(json.dumps({'axioms':axioms,'all_standard_three_only':True},indent=2)+'\n')
(OUT/'fresh-checks.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':'PASS','fresh_commands':3,'definition_audits':len(axioms),'pins':10,'holes':8}),flush=True)
