"""Freeze RA-09 statements and diagnostics before two independent approvals."""
from pathlib import Path
import datetime, hashlib, json, subprocess
P = Path(__file__).resolve().parents[1]
E = P/'reviews/statement-evidence'
W = P.parents[2]
BASE = '5830ed4fb06da0659414a3deb2a40ad327aca052'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert subprocess.check_output(['git','-C',str(W),'rev-parse','HEAD']).decode().strip() == BASE
assert not (P/'Solution.lean').exists() and not (P/'NLA/RA09/Proof.lean').exists()
assert not any((P/'reviews').glob('statement-referee-*.md'))
audit = json.loads((E/'input-audit.json').read_text())
assert audit['status'].startswith('PASS') and audit['completed_contracts'] == 0
freeze = P/'reviews/statement-freeze.json'
assert not freeze.exists()
excluded = {'reviews/statement-freeze.json','reviews/statement-handoff.md'}
files = {str(f.relative_to(P)):sha(f) for f in sorted(P.rglob('*'))
    if f.is_file() and str(f.relative_to(P)) not in excluded
    and not any(x in f.relative_to(P).parts for x in ['.lake','.verification','__pycache__'])
    and f.suffix not in ['.olean','.ilean','.trace','.pyc']}
S = json.loads((E/'source-inputs.json').read_text())
record = {'phase':'statement-only-before-two-independent-approvals',
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'base':BASE,
 'branch':'codex/lean-ra09-concave-frobenius-transfer','canonical_status':'Solved, unchanged',
 'statement_author':'/root/leancert_examples',
 'independent_statement_reviewers_required':['/root','/root/formal_review_standards'],
 'independent_approvals_present_at_freeze':False,'file_count':len(files),'files':files,
 'source_file_count':S['source_count'],'source_files':S['sources'],'source_git_blobs':S['git_blobs'],
 'intentional_Challenge_placeholders':17,'proof_or_Solution_exists':False,
 'actual_latest_statement_commands':3,'standard_three_structural_kernel_audits':17,
 'computation_scope':'Pure exact unbounded scalar algebra and generic finite matrices. No interval computation or artificial numerical singleton. LeanCert kernel trust/dependency audit is required for all eventual exports.',
 'source_integrity':'All original files unchanged at the exact Git base',
 'boundary':['NLA/RA09/Definitions.lean','Challenge.lean','NUMERICAL_TARGETS.md',
   'SourceCorrespondence.md','comparator.json','lakefile.toml','lake-manifest.json','lean-toolchain'],
 'self_and_later_handoff_exclusions':sorted(excluded),
 'generated_exclusions':['.lake','.verification','__pycache__','*.olean','*.ilean','*.trace','*.pyc'],
 'requirements':'No implementation before two independent approvals of these exact statements and configuration. All 17 full contracts required; genuine CFC/Frobenius/order/eigenbasis/scalar/harmonic bridges must discharge the full original trace-deficit universal implication. No f0=0, preferred-basis, matrix-commutation, scalar-certificate, spectral-formula or residual-premise substitution is permitted.'}
freeze.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'freeze_sha256':sha(freeze),'project_file_count':len(files),
 'original_source_count':S['source_count'],
 'boundary_sha256':{r:files[r] for r in record['boundary']},
 'input_audit_sha256':sha(E/'input-audit.json'),
 'reconstruction_sha256':sha(E/'exact-reconstruction.json')},indent=2))
