"""Run only the source/receipt/tool identity prefix while full Linux is pending.

This is not the final operational audit. The full driver, including final run
success and all controls, must pass separately before an operational verdict.
"""
from pathlib import Path
import ast
import hashlib
import json

p = Path(__file__).resolve().parent
driver = p / 'audit_checks.py'
text = driver.read_text()
prefix = text[:text.index("run = json.loads((OUT / 'run-metadata.json').read_text())")]
ast.parse(prefix)
namespace = {'__file__': str(driver), '__name__': '__source_identity_precheck__'}
exec(compile(prefix, str(driver) + ':identity-prefix', 'exec'), namespace)
record = {
    'status': 'Source and actual completed project receipt identities PASS; full Linux workflow and operational verdict pending',
    'driver_sha256': hashlib.sha256(driver.read_bytes()).hexdigest(),
    'actual_project_result': namespace['receipt']['result'],
    'committed_input_count': namespace['input_count'],
    'copied_dependency_artifacts': False,
    'full_operational_verdict': False,
    'reviewer_role': namespace['CTX']['role']}
(p / 'source-precheck.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
