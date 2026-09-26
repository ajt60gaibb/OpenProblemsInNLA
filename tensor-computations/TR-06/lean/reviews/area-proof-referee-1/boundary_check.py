from pathlib import Path
import hashlib,json,os,subprocess
root=Path(__file__).resolve().parent
challenge=Path('/private/tmp/tr06-review1/revised-frozen/Challenge.lean')
area=root/'source/NLA/TR06/Area.lean'
def hdr(p):
    s=p.read_text(); i=s.index('theorem induced_volume_chart '); return s[i:s.index(':= by',i)]
a,b=hdr(challenge),hdr(area)
assert a==b
proof='import NLA.TR06.Area\n\nnoncomputable section\nopen scoped ENNReal MeasureTheory\nopen MeasureTheory\nnamespace NLA.TR06.IndependentAreaReview\n'+a.replace('theorem induced_volume_chart','theorem exact_reviewed_target')+':= by\n  exact NLA.TR06.induced_volume_chart c s hs hsub\n#print axioms exact_reviewed_target\n#assert_trust kernel exact_reviewed_target\nend NLA.TR06.IndependentAreaReview\n'
p=root/'source/ReviewBoundary.lean';p.write_text(proof)
base=json.loads((root/'fresh-rerun.json').read_text())[0]
env=os.environ.copy();env['LEAN_PATH']=base['LEAN_PATH']
cmd=[base['command'][0],'-o',str(root/'build/ReviewBoundary.olean'),'ReviewBoundary.lean']
r=subprocess.run(cmd,cwd=root/'source',env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
log=root/'logs/ReviewBoundary.log';log.write_text(r.stdout)
record={'challenge_sha256':hashlib.sha256(challenge.read_bytes()).hexdigest(),'area_sha256':hashlib.sha256(area.read_bytes()).hexdigest(),'header_byte_identical':True,'review_boundary_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'exit_code':r.returncode,'command':cmd,'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()}
(root/'boundary-check.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2));print(r.stdout)
raise SystemExit(r.returncode)
