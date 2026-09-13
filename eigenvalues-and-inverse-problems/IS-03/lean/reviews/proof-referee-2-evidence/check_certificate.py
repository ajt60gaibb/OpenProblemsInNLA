"""Run the separate literal-input/kernel-reduction check on the fresh proof prefix."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
out=Path(__file__).resolve().parent;project=out.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,o):(out/n).write_text(json.dumps(o,indent=2)+'\n')
record=json.loads((out/'environment.json').read_text())
prior=json.loads((out/'fresh-result.json').read_text());assert prior['result']=='PASS'
prefix=Path(record['fresh_prefix']);source='reviews/proof-referee-2-evidence/Certificate.lean';target=prefix/'IndependentCertificate.olean'
assert not target.exists()
env=os.environ.copy();env['LEAN_PATH']=record['LEAN_PATH'];cmd=[record['lean'],'-o',str(target),source]
start=time.monotonic();r=subprocess.run(cmd,cwd=project,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
(out/'Certificate.log').write_bytes(r.stdout)
write('certificate-command.json',{'command':cmd,'exit_code':r.returncode,'seconds':round(time.monotonic()-start,3),'source_sha256':sha(project/source),'log_sha256':sha(out/'Certificate.log'),'object_sha256':sha(target) if target.exists() else None})
assert r.returncode==0,r.stdout.decode()
text=r.stdout.decode();assert not any(x in text for x in ['warning:','error:','sorryAx','Lean.ofReduceBool','Lean.trustCompiler'])
rows=[]
for name,body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text):
    axioms=set(x.strip() for x in body.split(',') if x.strip());assert axioms<={'propext','Classical.choice','Quot.sound'}
    rows.append({'name':name,'axioms':sorted(axioms)})
for name in re.findall(r"'([^']+)' does not depend on any axioms",text):rows.append({'name':name,'axioms':[]})
assert len(rows)==2
assert 'NLA.IS03.numerical_negative_moment._proof_1_7' in text
write('certificate-result.json',{'result':'PASS','actual_retained_helper':'NLA.IS03.numerical_negative_moment._proof_1_7','actual_input_checked_by_type_identity':True,'same_finite_boolean_recomputed_by_decide_kernel':True,'rational_expression':'(-8593) * (1/823543)','dummy_interval':['0','0'],'strict_upper_bound':'0','precision':-53,'taylor_depth':10,'kernel_assertions':rows,'scope':'Actual scalar-certificate consumption and exact finite Boolean replay only; no new matrix theorem or Linux verifier.'})
print('PASS: actual retained helper type and independent exact kernel Boolean reduction')
