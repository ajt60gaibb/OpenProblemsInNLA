"""Additional IS-03 original workflow/control evidence inspection; no source edits."""
from pathlib import Path
import json, re, hashlib, zipfile
O=Path(__file__).resolve().parent
C=json.loads((O/'audit-context.json').read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(O/n).write_text(json.dumps(j,indent=2)+'\n')
J=json.loads((O/'jobs.json').read_text())
JP=json.loads((O/'jobs-page-1.json').read_text())
assert J['jobs']==JP['jobs'] and len(J['jobs'])==J['total_count']==JP['total_count']==12
A=json.loads((O/'artifact-metadata.json').read_text())
AP=json.loads((O/'artifact-metadata-page-1.json').read_text())
assert A['artifacts']==AP['artifacts'] and len(A['artifacts'])==A['total_count']==AP['total_count']
IJ=json.loads((O/'permanent-id-jobs.json').read_text())
IP=json.loads((O/'permanent-id-jobs-page-1.json').read_text())
assert IJ['jobs']==IP['jobs'] and IJ['total_count']==IP['total_count']==len(IP['jobs'])==1
V=next((O/'artifacts/lean-IS-03').glob('verify-*'))
S=next((O/'artifacts/lean-checker-controls').glob('selftest-*'))
def normalized(s):
    s=re.sub(r'\b[0-9a-f]{32}\b','INVOCATION',s)
    s=re.sub(r'\([0-9.]+[m]?s\)','(TIME)',s)
    s=re.sub(r'((?:Service runtime|CPU time consumed|Memory peak|Memory swap peak): ).*',r'\1RESOURCE',s)
    return re.sub(r'nla-axiom-[a-z0-9_]+','nla-axiom-FRESH',s)
records={}
for f in ['sandbox.log','kernel-controls.log','comparator-controls.log','negative-native.log','negative-sorry.log','user-service.log']:
    a,b=(V/f).read_text(),(S/f).read_text()
    assert normalized(a)==normalized(b),f
    records[f]={'project_sha256':sha((V/f).read_bytes()),'standalone_sha256':sha((S/f).read_bytes()),'complete_substantive_text_equal':True,'normalized_sha256':sha(normalized(a).encode())}
save('full-control-correspondence.json',{'result':'PASS','normalization':'Only ephemeral invocation IDs, fresh axiom directory names, elapsed times and reported resource measurements; no commands, semantic phases, error codes, outcomes, environment settings, exports or control labels removed. Complete normalized contents agree. Both original byte-distinct executions retained.','files':records})
selected=[j for j in J['jobs'] if j['name'] in ['select','checker-controls'] or j['name'].startswith('verify (IS-03,')]
reviewed={}
for j in selected:
    f=O/f"job-{j['id']}.log";t=f.read_text()
    assert 'Ubuntu' in t and 'Ubuntu2404-Readme.md' in t
    assert C['commit'] in t
    reviewed[f.name]={'sha256':sha(f.read_bytes()),'lines':len(t.splitlines()),'job':j['name'],'steps':j['steps'],
        'phase_lines':[x for x in t.splitlines() if any(k in x for k in ['##[group]Run ', 'Ubuntu2404-Readme.md','SHA256 digest of uploaded','Artifact ID','Manifest schema and comparator coverage:','Ran ','Your solution is okay!','Lean default kernel accepts','Illegal axiom detected:','PASS: all'])]}
# Inspect actual preparation and runner commands, not only artifact summaries.
for j in selected:
    if j['name']=='select':continue
    t=(O/f"job-{j['id']}.log").read_text()
    for marker in ['sudo apt-get update','bubblewrap','uid','ulimit -n 65536','tools/lean/bootstrap.sh', '$RUNNER_TEMP/nla-lean-tools']:
        assert marker in t,(j['name'],marker)
    assert '--skip-kernel' not in t
# Whole run archives are retained without claiming other project's semantic audits.
with zipfile.ZipFile(O/'run-logs.zip') as z:
    entries=[i.filename for i in z.infolist() if not i.is_dir()]
    assert len(entries)==152 and z.testzip() is None
    full=[n for n in entries if '/' not in n]
    assert len(full)==12
    for j in selected:
        candidates=[n for n in full if n.endswith('_'+j['name'].replace('/','_')+'.txt')]
        # Actual GitHub archive uses sanitized path labels; selected job association
        # is additionally bound by source SHA and retained authenticated job IDs.
        if not candidates:
            candidates=[n for n in full if ('IS-03' in n if j['name'].startswith('verify (IS-03,') else n.endswith('_'+j['name']+'.txt'))]
        assert len(candidates)==1,(j['name'],full)
        archive_text=z.read(candidates[0]).decode()
        raw_text=(O/f"job-{j['id']}.log").read_text()
        assert archive_text==raw_text,(j['name'],'archive/job raw mismatch')
        reviewed[f"job-{j['id']}.log"]['identical_original_full_run_zip_entry']=candidates[0]
save('workflow-phase-review.json',{'result':'PASS','complete_jobs':12,'complete_run_log_files':152,'whole_job_logs':12,'observed_OS':'Ubuntu 24.04 x86_64, runner image ubuntu24/20260907.300','raw_metadata_page_identity':True,'original_artifact_metadata_count':A['total_count'],'manual_read_scope':'Actual main comparator, both complete raw controls via complete normalized identity, all bootstrap logs, dependency/cache phases, and selected workflow commands/outcomes read by independent agent. Complete unrelated logs retained; no additional semantic audit of unrelated project artifacts claimed.','reviewed_selected_jobs':reviewed})
print('PASS: complete controls, original metadata pages, actual runner phases, and full 152-file run-log archive; selected raw job logs byte-identical to original archive entries.')
