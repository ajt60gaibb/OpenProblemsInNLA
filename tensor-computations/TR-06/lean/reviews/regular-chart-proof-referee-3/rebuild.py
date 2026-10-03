from pathlib import Path
import os,subprocess,json,hashlib,datetime,re,sys
root=Path(__file__).resolve().parent
srcroot=root/'src';build=root/'build';logs=root/'logs'
for p in [srcroot,build,logs]:p.mkdir(exist_ok=True)
source_paths={
'Definitions':Path('/Users/ajt253/.codex/worktrees/tr06-formal-verification/OpenProblemsInNLA/tensor-computations/TR-06/lean/NLA/TR06/Definitions.lean'),
'ClosedFibers':Path('/private/tmp/tr06-proof-algebraic/NLA/TR06/ClosedFibers.lean'),
'RankOneCharts':Path('/private/tmp/tr06-proof-root/NLA/TR06/RankOneCharts.lean')}
for mod in ['RegularChartDefinitions','AdditionNoEscape','AdditionOpen','ImmersionPatch','PivotChart','RegularChart','RegularChartAudit']:
 source_paths[mod]=Path('/private/tmp/tr06-proof-regular-chart/NLA/TR06')/(mod+'.lean')
packages=Path('/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.lake/packages')
binary='/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.tools/lean-4.33.1-darwin_aarch64/bin/lean'
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(build),'/private/tmp/tr06-leancert/.lake/build/lib/lean']+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if (p/'.lake/build/lib/lean').exists()])
receipt={'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'fresh_project_modules':True,'project_olean_inputs_reused':False,'lean_path':env['LEAN_PATH'],'compiler_version':subprocess.run([binary,'--version'],text=True,capture_output=True).stdout.strip(),'runs':[]}
for mod,source in source_paths.items():
 data=source.read_bytes(); dest=srcroot/'NLA/TR06'/(mod+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 obj=build/'NLA/TR06'/(mod+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 if obj.exists():raise RuntimeError('Refusing reuse: '+str(obj))
 cmd=[binary,'-o',str(obj),str(dest)]
 run=subprocess.run(cmd,cwd=srcroot,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 log=logs/(mod+'.log');log.write_text(run.stdout)
 item={'module':'NLA.TR06.'+mod,'source':str(source),'copied_source':str(dest),'sha256':hashlib.sha256(data).hexdigest(),'command':cmd,'exit_code':run.returncode,'log':str(log),'output_has_warning':'warning:' in run.stdout,'output_has_sorry_axiom':'sorryAx' in run.stdout}
 if obj.exists():item['olean_sha256']=hashlib.sha256(obj.read_bytes()).hexdigest()
 receipt['runs'].append(item);(root/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(mod,run.returncode,flush=True)
 if run.returncode:print(run.stdout);sys.exit(run.returncode)
print('ALL TEN MODULES REBUILT FROM SOURCE',flush=True)
