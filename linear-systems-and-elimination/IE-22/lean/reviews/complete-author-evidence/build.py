"""Fresh full project-source author build; not authoritative Linux verification."""
from pathlib import Path
import os, subprocess, tempfile, json, hashlib, re, datetime

project=Path(__file__).resolve().parents[2]
review=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
boundary=json.loads((project/'reviews/statement-freeze.json').read_text())['mathematical_boundary_sha256']
for f,h in boundary.items():assert sha(project/f)==h,f
vendored=json.loads((project/'reviews/IE21-DEPENDENCY.json').read_text())['source_sha256']
for f,h in vendored.items():assert sha(project/f)==h,f
sources={str(p.relative_to(project)):sha(p) for p in sorted((project/'NLA').rglob('*.lean'))}
assert len(vendored)==31
order=[]
visiting=set()
done=set()
def visit(name):
    if name in done:return
    assert name not in visiting,('import cycle',name)
    visiting.add(name)
    path=name.replace('.','/')+'.lean'
    assert path in sources,path
    for imported in re.findall(r'^import (NLA\.[\w.]+)',(project/path).read_text(),re.M):visit(imported)
    visiting.remove(name);done.add(name);order.append(path)
for path in sources:visit(path[:-5].replace('/','.'))
args={
'supremum_semantics':'θ hθ m n hm hn','constant_semantics':'θ hθ',
'projection_semantics':'θ hθ m n d hn hd A J','spectral_projection':'m n r hm hr A hA',
'gaussian_objective_mean':'θ hθ m d hm hd B hB t ht',
'gaussian_objective_variance':'θ m d hm hd B t ht','gaussian_energy_moments':'m d hm hd B',
'bounded_trimming_threshold':'θ hθ m hm y hy hmean','threshold_lipschitz':'θ hθ m hm y s t',
'threshold_grid':'θ hθ δ hδ','projection_good_event_bound':'θ hθ m d r hm hd hr B hrows hop δ hδ',
'deterministic_finite_bound':'θ hθ m n r hm hr δ hδ hfail A hA',
'supremum_finite_bound':'θ hθ m n r hm hr δ hδ hfail','deterministic_schedule':'θ hθ',
'universal_squared_rate':'θ hθ','uniform_upper_all_rows':'θ hθ ε hε',
'spherical_realization_from_finite_bound':'θ hθ m n hm hn t ε δ ht hε hδ hfail',
'high_aspect_near_extremizers':'θ hθ m n hm hn hnlim hQlim ε hε',
'high_aspect_supremum_limit':'θ hθ m n hm hn hnlim hQlim','canonical_sharp_constant':'θ hθ'}
config=json.loads((project/'comparator.json').read_text())
assert list(args)==[x.removeprefix('NLA.IE22.') for x in config['theorem_names']]
audit='import NLA.IE22.Final\nset_option autoImplicit false\nnoncomputable section\nopen MeasureTheory ProbabilityTheory Filter Set\nopen scoped BigOperators ENNReal RealInnerProductSpace Topology\nopen NLA.IE21 NLA.IE22\n\n'
challenge=(project/'Challenge.lean').read_text()
for name,arg in args.items():
    matched=re.search(r'theorem '+name+r'\b[\s\S]*? := by sorry',challenge)
    assert matched,name
    audit+=matched[0].replace('theorem '+name,'example',1).replace('by sorry','by\n  exact NLA.IE22.'+name+' '+arg)+'\n#print axioms NLA.IE22.'+name+'\n\n'
(review/'ExactTypesAndAxioms.lean').write_text(audit)
build=Path(tempfile.mkdtemp(prefix='nla-ie22-complete-author-',dir='/private/tmp'))
packages=Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
lean='/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean'
env=dict(os.environ)
env['LEAN_PATH']=os.pathsep.join([str(build),str(project)]+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()])
commands=[]
with (review/'typecheck.log').open('w') as log:
    log.write('All NLA project sources rebuilt, including 31 unchanged IE21 modules. Local cached dependencies; no authoritative Linux/LeanCert/Comparator claim.\n')
    log.write(subprocess.check_output([lean,'--version'],text=True))
    for path in order+['reviews/complete-author-evidence/ExactTypesAndAxioms.lean']:
        out=build/Path(path).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
        cmd=[lean,'-o',str(out),path]
        res=subprocess.run(cmd,cwd=project,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        log.write('COMMAND '+json.dumps(cmd)+'\n'+res.stdout+'EXIT '+str(res.returncode)+'\n');log.flush()
        commands.append({'source':path,'command':cmd,'exit_code':res.returncode,'output':res.stdout})
        print(path,res.returncode,flush=True)
        if res.returncode or 'warning:' in res.stdout:
            print(res.stdout,flush=True)
            raise SystemExit('Fresh build failed or needs warning review; no completion receipt created')
assert sources=={f:sha(project/f) for f in sources}
for f,h in boundary.items():assert sha(project/f)==h,f
output=commands[-1]['output']
for name in config['theorem_names']:
    assert "'"+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in output,name
r={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'role':'Author aggregate check, not final nonauthor review',
   'project_sources_built':len(sources),'vendored_IE21_sources_built':31,'build_directory':str(build),
   'source_hashes':sources,'mathematical_boundary_sha256':boundary,'selected_target_count':20,
   'all_selected_targets_compiled':True,'exact_full_frozen_types':True,'allowed_axioms':config['permitted_axioms'],
   'commands':commands,'log_sha256':sha(review/'typecheck.log'),'audit_sha256':sha(review/'ExactTypesAndAxioms.lean'),
   'limits':['Cached pinned Mathlib dependency objects used','Authentic LeanCert wrapper and Linux Comparator remain pending','Final nonauthor whole-source reviews remain pending']}
(review/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print('PASS fresh complete project-source build and all 20 exact selected type/axiom checks')
