from pathlib import Path
import datetime, hashlib, json, os, platform, re, subprocess, tempfile, time
P=Path('/tmp/nla-lean-mf16-worktree/matrix-functions-and-stability/MF-16/lean')
R=P.parents[2]
OUT=P/'reviews/final-referee-1-evidence'
PREP=Path('/tmp/nla-lean-formalization/mf16-final-referee1-prep')
D=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
L=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
git=lambda p,*args:subprocess.check_output(['git','-C',str(p),*args])
OUT.mkdir(exist_ok=True)
def save(name,value): (OUT/name).write_text(json.dumps(value,indent=2)+'\n')
FZ='f4b21be066d0e55e56aae5b3fd1119433ef09d7ed5822d57dacab906b38ac720'
HO='ad86420d1e3640da6c2edacfc4160a259a766a59764f1f764ca4caa7e1082f78'
assert sha(P/'verification/proof-freeze.json')==FZ
assert sha(P/'reviews/proof-completion.md')==HO
F=json.loads((P/'verification/proof-freeze.json').read_text())
S=json.loads((P/'reviews/statement-freeze.json').read_text())
def integrity():
    assert sha(P/'verification/proof-freeze.json')==FZ
    assert sha(P/'reviews/proof-completion.md')==HO
    assert sha(P/'reviews/statement-freeze.json')=='eaba8311f143727f2061f2b4c945e403e62b7e9041712d983ef56ccf2e7f0587'
    assert len(F['files'])==182 and len(F['source_files'])==14
    for rel,h in F['files'].items(): assert sha(P/rel)==h,rel
    for rel,h in S['files'].items(): assert sha(P/rel)==h,rel
    assert len(S['files'])==45
    source=[]
    for rel,h in F['source_files'].items():
        raw=git(R,'show',F['base']+':'+rel)
        assert hashlib.sha256(raw).hexdigest()==h and raw==(R/rel).read_bytes(),rel
        source.append({'path':rel,'sha256':h,'base_blob':git(R,'rev-parse',F['base']+':'+rel).decode().strip()})
    return {'result':'PASS','freeze_sha256':FZ,'handoff_sha256':HO,
        'project_input_count':182,'statement_input_count':45,
        'project_inputs':F['files'],'original_sources':source}
before=integrity()
save('integrity-before.json',before)
(OUT/'Inspect.lean').write_bytes((PREP/'Inspect.lean').read_bytes())
(OUT/'fresh_review.py').write_bytes(Path(__file__).read_bytes())
def headers(path):
    txt=path.read_text()
    out={}
    for m in re.finditer(r'^theorem\s+(\w+)\s+',txt,re.M):
        finish=txt.index(':=',m.end())
        out[m.group(1)]=' '.join(txt[m.end():finish].split())
    return out
H=headers(P/'Challenge.lean')
assert H==headers(P/'Solution.lean') and len(H)==9
cfg=json.loads((P/'comparator.json').read_text())
assert cfg['theorem_names']==['NLA.MF16.'+n for n in H]
assert cfg['definition_names']==[]
assert cfg['permitted_axioms']==['propext','Classical.choice','Quot.sound']
save('source-signatures.json',{'result':'PASS','signatures':H,'comparator_configuration':cfg,
 'scope':'Normalized source headers and fresh elaboration, not actual Comparator execution'})
mods=['NLA/MF16/Definitions.lean','NLA/MF16/Numerical.lean','NLA/MF16/Algebra.lean',
      'NLA/MF16/Recovery.lean','NLA/MF16/Polynomial.lean','NLA/MF16/CayleyHamilton.lean',
      'NLA/MF16/Proof.lean','Solution.lean']
scan={}
for m in mods:
    txt=(P/m).read_text()
    code=re.sub(r'/\-.*?\-/','',txt,flags=re.S)
    code=re.sub(r'--[^\n]*','',code)
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|partial|native_decide)\b',code),m
    assert not re.search(r'^import\s+Challenge\b',code,re.M),m
    assert not any(x in code for x in ['debug.skipKernelTC','trustCompiler','ofReduceBool'])
    scan[m]={'sha256':sha(P/m),'result':'PASS'}
save('source-scan.json',scan)
def pins():
    out=[]
    for pkg in json.loads((P/'lake-manifest.json').read_text())['packages']:
        p=D/pkg['name']
        rev=git(p,'rev-parse','HEAD').decode().strip()
        assert rev==pkg['rev'] and git(p,'status','--porcelain=v1')==b'',pkg['name']
        out.append({'name':pkg['name'],'path':str(p.resolve()),'revision':rev,'clean':True})
    assert len(out)==10
    return out
pinned=pins()
save('dependency-pins-before.json',pinned)
prefix=Path(tempfile.mkdtemp(prefix='mf16-final-referee1-',dir='/tmp/nla-lean-formalization/independent-prefixes'))
assert not any(prefix.iterdir())
paths=[prefix,*[D/n/'.lake/build/lib/lean' for n in ['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib','leancert']],L/'lib/lean']
env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,paths)))
record={'result':'RUNNING','reviewer':'/root/mf16_final_referee','independent_AI_agent':True,
 'no_statement_or_proof_contribution':True,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'platform':platform.platform(),'toolchain':subprocess.check_output([str(L/'bin/lean'),'--version'],text=True).strip(),
 'fresh_prefix':str(prefix),'LEAN_PATH':env['LEAN_PATH'],'empty_project_prefix_before_build':True,
 'old_project_objects_excluded':True,'dependency_objects_read_only':True,
 'dependency_copy_download_rebuild':False,'local_Lake_invocation':False,'Linux_Comparator_run':False,'commands':[]}
save('fresh-checks.json',record)
for m in mods+['Challenge.lean','reviews/final-referee-1-evidence/Inspect.lean']:
    cmd=[str(L/'bin/lean')]
    objects=[]
    if not m.endswith('/Inspect.lean'):
        for flag,ext in [('-o','.olean'),('-i','.ilean')]:
            obj=prefix/Path(m).with_suffix(ext)
            obj.parent.mkdir(parents=True,exist_ok=True)
            cmd.extend([flag,str(obj)]);objects.append(obj)
    cmd.append(m)
    started=time.monotonic()
    print('Fresh independent compile:',m,flush=True)
    run=subprocess.run(cmd,cwd=P,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=OUT/(m.removesuffix('.lean').replace('/','-')+'.log')
    log.write_bytes(run.stdout)
    row={'source':m,'source_sha256':sha(P/m),'command':cmd,
         'exit_code':run.returncode,'seconds':time.monotonic()-started,
         'log':log.name,'log_sha256':sha(log),
         'fresh_objects':{str(o.relative_to(prefix)):sha(o) for o in objects if o.exists()}}
    record['commands'].append(row);save('fresh-checks.json',record)
    print('Exit:',run.returncode,round(row['seconds'],3),'seconds',flush=True)
    if run.returncode!=0:
        print(run.stdout.decode(),flush=True)
        raise SystemExit(run.returncode)
    count=9 if m=='Challenge.lean' else 0
    assert run.stdout.count(b'warning:')==count,run.stdout.decode()
    assert run.stdout.count(b'declaration uses '+bytes([96])+b'sorry'+bytes([96]))==count,run.stdout.decode()
    assert b'error:' not in run.stdout
    assert sha(P/m)==row['source_sha256']
axioms=[]
for row in record['commands']:
    for name,a in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(OUT/row['log']).read_text()):
        aa=[x.strip() for x in a.split(',') if x.strip()]
        assert set(aa)<=set(cfg['permitted_axioms']),(name,aa)
        axioms.append({'declaration':name,'axioms':aa,'log':row['log']})
assert len(axioms)==26,len(axioms)
save('axioms.json',{'result':'PASS','count':len(axioms),'standard_three_or_subset_only':True,'reports':axioms})
inspection=(OUT/'reviews-final-referee-1-evidence-Inspect.log').read_text()
counts=re.findall(r'^REFEREE_COUNTS (\w+): project=(\d+), library=(\d+)',inspection,re.M)
assert len(counts)==2
required=re.findall(r'^REFEREE_REQUIRED (\w+): (\S+)',inspection,re.M)
assert len(required)==60,len(required)
save('actual-proof-dependencies.json',{'result':'PASS','counts':counts,'required_per_closure':30,
 'final_target_separately_traversed':True,'actual_type_and_value_traversal':True,
 'required_consumed':required})
numeric=[s.split('=',1)[1] for s in inspection.splitlines() if s.startswith('REFEREE_NUMERIC_JSON=')]
assert len(numeric)==1
save('actual-numeric.json',json.loads(numeric[0]))
after=integrity();save('integrity-after.json',after)
assert before==after
assert pins()==pinned
save('dependency-pins-after.json',pinned)
record.update(result='PASS',completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
save('fresh-checks.json',record)
print(json.dumps({'result':'PASS','commands':len(record['commands']),'axiom_reports':len(axioms),'closure_counts':counts}))
