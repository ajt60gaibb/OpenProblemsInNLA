"""Independent IS03 statement-referee driver; expects a parent-confirmed freeze.

No candidate source is edited. Only new referee outputs and a fresh object prefix
are written. MI22 dependency source/object trees are read-only throughout.
"""
from pathlib import Path
import datetime,hashlib,json,os,platform,re,subprocess,sys,tempfile,time
OUT=Path(__file__).resolve().parent
PROJECT=OUT.parents[1]
REPO=PROJECT.parents[2]
DEPS=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
LEAN=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean')
expected_freeze,expected_handoff=sys.argv[1:3]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
save=lambda name,data:(OUT/name).write_text(json.dumps(data,indent=2)+'\n')
assert sha(PROJECT/'reviews/statement-freeze.json')==expected_freeze
assert sha(PROJECT/'reviews/statement-handoff.md')==expected_handoff
f=json.loads((PROJECT/'reviews/statement-freeze.json').read_text())
base=f.get('base') or f.get('source_commit')
assert base=='f41f1f9ffa2171550d4bb795862c6170c4f26070'
def digest(entry):return entry['sha256'] if isinstance(entry,dict) else entry
def integrity():
    for rel,entry in f['files'].items():
        assert sha(PROJECT/rel)==digest(entry),rel
        if isinstance(entry,dict) and 'bytes' in entry:
            assert (PROJECT/rel).stat().st_size==entry['bytes'],rel
    originals={}
    for rel,entry in f['source_files'].items():
        raw=subprocess.check_output(['git','show',base+':'+rel],cwd=REPO)
        assert hashlib.sha256(raw).hexdigest()==digest(entry),rel
        assert raw==(REPO/rel).read_bytes(),rel
        originals[rel]={'sha256':digest(entry),
            'git_blob':subprocess.check_output(['git','rev-parse',base+':'+rel],cwd=REPO,text=True).strip()}
    assert not (PROJECT/'NLA/IS03/Proof.lean').exists()
    assert not (PROJECT/'Solution.lean').exists()
    return {'status':'PASS','freeze_sha256':expected_freeze,'handoff_sha256':expected_handoff,
        'project_count':len(f['files']),'source_count':len(originals),
        'project_inputs':f['files'],'source_inputs':originals,'proof_absent':True,'source_commit':base}
before=integrity();save('integrity-before.json',before)

cfg=json.loads((PROJECT/'comparator.json').read_text())
text=(PROJECT/'Challenge.lean').read_text()
declarations=re.findall(r'^theorem\s+(\w+)\s+(.*?)\s*:=\s*by\s+sorry',text,re.M|re.S)
names=['NLA.IS03.'+name for name,_ in declarations]
assert len(names)==7 and text.count('sorry')==7
assert cfg['theorem_names']==names
assert cfg['definition_names']==[]
assert cfg['challenge_module']=='Challenge' and cfg['solution_module']=='Solution'
assert set(cfg['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert f.get('export_names',names)==names
definitions=(PROJECT/'NLA/IS03/Definitions.lean').read_text()
assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',definitions)
assert not re.search(r'^theorem\s',definitions,re.M)
save('statement-boundary.json',{'status':'PASS','count':7,'names':names,
    'signatures':{name:' '.join(sig.split()) for name,sig in declarations},
    'comparator_sha256':sha(PROJECT/'comparator.json'),'definition_exceptions':[],
    'scope':'Approved statement boundary only; no Solution proof exists and no actual Comparator run is claimed.'})

pins=[]
for pkg in json.loads((PROJECT/'lake-manifest.json').read_text())['packages']:
    path=DEPS/pkg['name']
    rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=path,text=True).strip()
    dirty=subprocess.check_output(['git','status','--porcelain'],cwd=path,text=True)
    assert rev==pkg['rev'] and not dirty,(pkg['name'],rev,dirty)
    pins.append({'name':pkg['name'],'revision':rev,'path':str(path),'git_status_porcelain':dirty})
assert len(pins)==10
save('dependency-pins.json',pins)
(PROJECT/'.verification').mkdir(exist_ok=True)
prefix=Path(tempfile.mkdtemp(prefix='is03-statement-referee1-',dir=PROJECT/'.verification'))
paths=[str(prefix)]+[str(DEPS/x['name']/'.lake/build/lib/lean') for x in reversed(pins)]+[str(LEAN.parent.parent/'lib/lean')]
env=dict(os.environ,LEAN_PATH=os.pathsep.join(paths))
record={'status':'RUNNING','reviewer':'/root/leancert_examples','independent_of_statement_authors':True,
    'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'platform':platform.platform(),
    'lean_version':subprocess.check_output([str(LEAN),'--version'],text=True).strip(),
    'dependency_root':str(DEPS),'dependency_artifacts_read_only':True,
    'dependency_rebuild':False,'old_project_objects_excluded':True,
    'fresh_prefix':str(prefix),'LEAN_PATH':env['LEAN_PATH'],
    'local_Lake_invocation':False,'Linux_Comparator_run':False,'commands':[]}
for rel in ['NLA/IS03/Definitions.lean','Challenge.lean','reviews/statement-referee-1-evidence/Inspect.lean']:
    cmd=[str(LEAN)];objects=[]
    if not rel.endswith('/Inspect.lean'):
        for flag,suffix in [('-o','.olean'),('-i','.ilean')]:
            dest=prefix/Path(rel).with_suffix(suffix);dest.parent.mkdir(parents=True,exist_ok=True)
            cmd.extend([flag,str(dest)]);objects.append(dest)
    cmd.append(rel);label=rel.removesuffix('.lean').replace('/','-')
    print('Independent fresh statement check',rel,flush=True)
    t=time.monotonic()
    cp=subprocess.run(cmd,cwd=PROJECT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=OUT/(label+'.log');log.write_bytes(cp.stdout)
    record['commands'].append({'source':rel,'source_sha256':sha(PROJECT/rel),'command':cmd,
        'exit_code':cp.returncode,'elapsed_seconds':time.monotonic()-t,'log':log.name,
        'log_sha256':sha(log),'fresh_objects':{str(x.relative_to(prefix)):sha(x) for x in objects if x.exists()}})
    save('fresh-checks.json',record)
    print('Exit',cp.returncode,flush=True)
    assert cp.returncode==0,cp.stdout.decode()
    warning_count=7 if rel=='Challenge.lean' else 0
    assert cp.stdout.count(b'warning:')==warning_count,cp.stdout.decode()
    assert cp.stdout.count(b'declaration uses `sorry`')==warning_count,cp.stdout.decode()
    assert b'error:' not in cp.stdout
raw=(OUT/'reviews-statement-referee-1-evidence-Inspect.log').read_text()
reports=[]
for line in raw.splitlines():
    m=re.fullmatch(r"'([^']+)' depends on axioms: \[([^\]]*)\]",line)
    if m:
        axioms=[re.sub(r'\.\{[^}]*\}','',x.strip()) for x in m.group(2).split(',') if x.strip()]
        assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(m.group(1),axioms)
        reports.append({'name':m.group(1),'axioms':axioms})
    m=re.fullmatch(r"'([^']+)' does not depend on any axioms",line)
    if m:reports.append({'name':m.group(1),'axioms':[]})
assert len(reports)==12,reports
save('definition-axioms.json',{'status':'PASS','count':12,'reports':reports,
    'scope':'Only actual definitions were audited. Seven deliberately admitted Challenge theorems remain unproved.'})
after=integrity();assert after==before
save('integrity-after.json',after)
record.update(status='PASS',fresh_commands=3,statement_exports=7,
    definition_kernel_audits=12,statement_placeholders=7,all_frozen_inputs_unchanged=True)
save('fresh-checks.json',record)
print(json.dumps({'status':'PASS','fresh_commands':3,'exports':7,'definition_kernel_audits':12,
    'project_inputs':len(f['files']),'original_sources':len(f['source_files']),'clean_pins':10}),flush=True)
