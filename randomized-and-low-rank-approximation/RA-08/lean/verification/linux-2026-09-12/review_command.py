from pathlib import Path
import datetime,hashlib,json,subprocess,sys,time
O=Path(__file__).resolve().parent
name=sys.argv[1];assert Path(name).name==name and name.endswith('.py')
script=O/name;assert script.exists()
a=O/'review-attempts'/(datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')+'-'+script.stem)
a.mkdir(parents=True,exist_ok=False)
sha=lambda b:hashlib.sha256(b).hexdigest()
(a/(name+'.txt')).write_bytes(script.read_bytes())
t=time.monotonic();r=subprocess.run([sys.executable,'-B',str(script)],cwd=O.parents[1],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(a/'raw.log').write_bytes(r.stdout)
record={'command':r.args,'cwd':str(O.parents[1]),'script_sha256':sha(script.read_bytes()),'exit_code':r.returncode,'seconds':time.monotonic()-t,'raw_log_sha256':sha(r.stdout),'source_snapshot':name+'.txt'}
(a/'result.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'attempt':str(a.relative_to(O)),'exit_code':r.returncode,'seconds':record['seconds']}));print(r.stdout.decode())
sys.exit(r.returncode)
