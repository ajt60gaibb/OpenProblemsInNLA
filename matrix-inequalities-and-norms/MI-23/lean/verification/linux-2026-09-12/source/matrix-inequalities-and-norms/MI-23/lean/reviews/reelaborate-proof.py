#!/usr/bin/env python3
"""Local author diagnostic: fresh project source elaboration against pinned cached dependencies.
This is not the authoritative Linux sandbox/export/replay/Comparator verification.
"""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, sys, time
project = Path(__file__).resolve().parent.parent
lake = Path('/Users/georgestepaniants/.elan/bin/lake')
lean = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean')
prefix = Path('/tmp/nla-lean-formalization/mi23-author-fresh')
prefix.mkdir(parents=True, exist_ok=True)
log_path = project / 'reviews/proof-source-build.log'
result_path = project / 'reviews/proof-source-build-result.json'
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
freeze = json.loads((project/'reviews/statement-freeze.json').read_text())
protected = ['NLA/MI23/Definitions.lean','Challenge.lean','NUMERICAL_TARGETS.md',
             'lean-toolchain','lake-manifest.json','comparator.json']
for rel in protected:
    assert sha(project/rel) == freeze['files'][rel]['sha256'], rel
pins = []
manifest = json.loads((project/'lake-manifest.json').read_text())
for p in manifest['packages']:
    repo = project/'.lake/packages'/p['name']
    rev = subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
    changes = subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=repo,text=True)
    assert rev == p['rev'] and not changes, p['name']
    pins.append({'name':p['name'],'rev':rev,'tracked_worktree_clean':True})
raw = subprocess.check_output([str(lake),'env','printenv','LEAN_PATH'],cwd=project,text=True).strip()
project_cache = (project/'.lake/build/lib/lean').resolve()
deps = [p for p in raw.split(os.pathsep) if p and Path(p).resolve() != project_cache]
env = dict(os.environ,LEAN_PATH=os.pathsep.join([str(prefix),*deps]))
modules = ['NLA/MI23/Definitions','NLA/MI23/FunctionalCalculus','NLA/MI23/SpectralNorm',
           'NLA/MI23/NormBounds','NLA/MI23/Witness','NLA/MI23/Arithmetic','NLA/MI23/Proof','Solution']
results = []
with log_path.open('w') as log:
    for mod in modules:
        src=project/(mod+'.lean'); out=prefix/(mod+'.olean'); info=prefix/(mod+'.ilean')
        out.parent.mkdir(parents=True,exist_ok=True)
        cmd=[str(lean),'-o',str(out),'-i',str(info),str(src)]
        log.write('COMMAND '+json.dumps(cmd)+'\n');log.flush()
        t=time.monotonic()
        proc=subprocess.run(cmd,cwd=project,env=env,stdout=log,stderr=subprocess.STDOUT)
        record={'module':mod,'exit_code':proc.returncode,'seconds':round(time.monotonic()-t,3),
                'source_sha256':sha(src)}
        results.append(record)
        print(json.dumps(record),flush=True)
        if proc.returncode: break
assert len(results)==len(modules) and all(x['exit_code']==0 for x in results), results
log_text=log_path.read_text()
assert not re.search(r'\b(?:error|warning):',log_text), log_path
axioms=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log_text)
assert len(axioms)==64,len(axioms)
for name, ax in axioms:
    assert set(a.strip() for a in ax.split(',')) == {'propext','Classical.choice','Quot.sound'},name
inspection=project/'reviews/proof-inspection.log'
with inspection.open('w') as log:
    cmd=[str(lean),str(project/'reviews/InspectProof.lean')]
    log.write('COMMAND '+json.dumps(cmd)+'\n');log.flush()
    proc=subprocess.run(cmd,cwd=project,env=env,stdout=log,stderr=subprocess.STDOUT)
assert proc.returncode==0
ins=inspection.read_text()
assert 'verify_strict_upper_bound_dyadic_checked' in ins
assert 'NLA.MI23.squaredGap_positive' in ins
assert 'NLA.MI23.witness_strict_norm_gap' in ins
assert 'NLA.MI23.witness_not_logMajorized' in ins
assert 'sorryAx' not in ins and 'Lean.ofReduceBool' not in ins
for rel in protected:
    assert sha(project/rel)==freeze['files'][rel]['sha256'],rel
result={'status':'PASS: fresh local project source elaboration; authoritative Linux checks pending',
        'host_scope':'macOS arm64; fresh project oleans, pinned cached dependencies',
        'started_utc':started,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'commands':results,'axiom_reports':len(axioms),'all_axiom_sets_exact_standard_three':True,
        'kernel_assertions':64,'all_core_statement_and_dependency_inputs_unchanged':True,
        'dependency_pins':pins,'project_cache_excluded':str(project_cache),
        'fresh_output_prefix':str(prefix),'log_sha256':sha(log_path),
        'inspection_log_sha256':sha(inspection),'inspection_exit_code':proc.returncode,
        'explicit_kernel_LeanCert_certificate_and_final_consumers_inspected':True}
result_path.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'result_sha256':sha(result_path)}),flush=True)
