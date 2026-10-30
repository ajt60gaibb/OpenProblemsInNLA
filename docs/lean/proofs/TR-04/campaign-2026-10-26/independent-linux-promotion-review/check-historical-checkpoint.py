#!/usr/bin/env python3
"""Bind historical pre-promotion evidence to its immutable Git checkpoint.

Historical receipts intentionally bind the former live metadata/README bytes;
after the approved promotion they are checked at that historical tree, not
mislabelled as current inputs.
"""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess
B=Path(__file__).resolve().parent;REPO=B.parents[5]
CHECKPOINT='e7b6c9c592d823973aac5d39a6dbe6c81c0005ce'
INDEX='docs/lean/proofs/TR-04/campaign-2026-10-26/independent-evidence-index/result-through-full-target-v2.json'
digest=lambda b:hashlib.sha256(b).hexdigest()
reader=subprocess.Popen(['git','cat-file','--batch'],cwd=REPO,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
def blob(path):
    assert '\n' not in path and '\r' not in path
    reader.stdin.write((CHECKPOINT+':'+path+'\n').encode());reader.stdin.flush()
    h=reader.stdout.readline().decode().rstrip('\n').split()
    assert len(h)==3 and h[1]=='blob',path
    n=int(h[2]);data=reader.stdout.read(n)
    assert len(data)==n and reader.stdout.read(1)==b'\n'
    return data
try:
    data=blob(INDEX);assert digest(data)=='6f7b795d432b495f0949c7f6d77c02e4ab3f2f62c89cff227955e9642c918b8e'
    index=json.loads(data);assert index['passed'] and index['approved_scopes']==42 and len(index['artifact_hashes'])==6349
    for path,h in index['artifact_hashes'].items():assert digest(blob(path))==h,path
    rawpath='docs/lean/proofs/TR-04/campaign-2026-10-26/independent-full-target-review/run-attempt-1/result.json'
    raw=json.loads(blob(rawpath));assert raw['passed'] is False and all(x['passed'] for x in raw['blocks'].values())
    terminalpath='docs/lean/proofs/TR-04/campaign-2026-10-26/independent-full-target-review/TERMINAL_VALIDATION.json'
    terminal=json.loads(blob(terminalpath));assert terminal['passed'] and not terminal['retained_original_aggregate_passed']
    assert terminal['all7_positive_scopes_rechecked_from_raw_logs'] and terminal['Challenge_target_exact_forbidden_sorryAx_rejected']
    out={'passed':True,'recorded_utc':datetime.now(timezone.utc).isoformat(),
         'reviewer':'/root/recover_verification','type':'historical_Git_checkpoint_artifact_integrity_only',
         'checkpoint':CHECKPOINT,'historical_index_path':INDEX,'historical_index_sha256':digest(data),
         'historical_artifacts_checked':6349,'approved_scopes':42,
         'all6349_historical_bytes_preserved_in_checkpoint':True,
         'original_false_aggregate_preserved':True,'separate_terminal_validation_preserved':True,
         'comparison_placeholder_accepted_as_proof':False,'new_Lean_or_Linux_execution':False,
         'historical_sources_relabelled_as_current':False,
         'checker_sha256':digest(Path(__file__).read_bytes()),
         'note':'Approved promotion changes live YAML and one display README. Historical receipts continue to refer to their original pre-promotion input context, independently verified here at the exact accepted-evidence Git checkpoint. Current final inputs are bound separately.'}
finally:
    reader.stdin.close();reader.wait()
p=B/'HISTORICAL_CHECKPOINT.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'historical_artifacts':6349,'sha256':digest(p.read_bytes())},indent=2))
