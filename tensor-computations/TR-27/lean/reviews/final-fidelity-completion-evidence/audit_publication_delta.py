#!/usr/bin/env python3
"""Check exactly the reviewed post-run documentation delta; no Lean execution."""
from pathlib import Path
import hashlib,json,subprocess
base=Path(__file__).resolve().parents[2]
repo=base.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
digest=lambda p:sha(p.read_bytes())
verified='775e8b169119c4045b07db7666eda8c001ae3bd1'
expected=json.loads((base/'verification/linux/input-receipt.json').read_text())['input_sha256']
allowed={
 'README.md':'a60de9d0e8fa80a99ca5d46f3ebec7f3d7ba0ed6e31bf1a53789d5f567fc2374',
 'formalization.yaml':'aff70ae2e8bfbf833ab832e5c7541876a788251bf28b180e9cce36b7efb1fbe9',
}
changed={k:digest(base/k) for k in expected if digest(base/k)!=expected[k]}
assert changed==allowed,changed
assert len(expected)-len(changed)==114
for k,h in expected.items():
 assert digest(base/'verification/linux/source'/k)==h,k
 if k not in allowed:assert digest(base/k)==h,k
old=subprocess.check_output(['git','show',verified+':tensor-computations/TR-27/README.md'],cwd=repo).decode()
current=(base.parent/'README.md').read_text()
assert digest(base.parent/'README.md')=='5591cb850a1517fc5997da0b8cb38c13b372417e8703f179ae5ca951c6903069'
heading='## Problem statement\n'
assert current.split(heading,1)[1]==old.split(heading,1)[1]
notice_heading='## Lean proof and verification evidence - 2026-09-22\n'
prefix,after=current.split(notice_heading,1)
prefix=prefix.replace('**Status:** Lean verified','**Status:** Solved').replace('**Last checked:** 2026-09-22','**Last checked:** 2026-09-17')
assert prefix==old.split(heading,1)[0]
assert current.splitlines()[0]==old.splitlines()[0]
registry=repo/'problem_ids.json'
assert registry.read_bytes()==subprocess.check_output(['git','show',verified+':problem_ids.json'],cwd=repo)
completion=json.loads((base/'reviews/final-fidelity-completion-receipt.json').read_text())
assert digest(base/'reviews/final-fidelity-referee.md')==completion['prior_report_sha256']
assert digest(base/'reviews/final-fidelity-source-receipt.json')==completion['prior_source_receipt_sha256']
assert digest(base/'reviews/final-fidelity-completion-evidence/audit.py')==completion['independent_audit_script_sha256']
assert digest(base/'reviews/final-fidelity-completion-evidence/audit.json')==completion['independent_audit_json_sha256']
notice=notice_heading+after.split(heading,1)[0]
normalized_notice=notice.replace('with:\n\n```\n', 'with:\n\n```sh\n', 1).replace(' \\\n  ', ' ').rstrip()+'\n\n'
assert sha(normalized_notice.encode())==completion['publication_notice_sha256']
resolved=(repo/'RESOLVED.md').read_text()
old_resolved=subprocess.check_output(['git','show',verified+':RESOLVED.md'],cwd=repo).decode()
start=resolved.index('**TR-27 Lean verification, 2026-09-22.**')
end=resolved.index('\n\n',start)+2
assert resolved[:start]+resolved[end:]==old_resolved
record={'reviewer':'/root/tr27_final_fidelity','role':'independent nonauthor AI referee','verified_source_commit':verified,
 'verdict':'PASS','allowed_documentation_delta_sha256':allowed,'strict_unchanged_input_count':114,
 'all_mathematical_build_and_comparator_files_unchanged':True,'retained_116_input_snapshot_unchanged':True,
 'original_problem_statement_and_remaining_sections_unchanged':True,'original_preface_and_attribution_unchanged_except_status_and_date':True,
 'permanent_registry_unchanged':True,'prior_report_receipt_and_audit_preserved':True,
 'canonical_readme_sha256':digest(base.parent/'README.md'),'notice_prose_matches_approval_except_code_fence_tag_shell_line_wrap_and_trailing_space':True,'published_notice_sha256':sha(notice.encode()),
 'scope':'Post-run prose/status publication delta only; PDF visual QA and repository ID/catalog gates are separate.'}
(base/'reviews/final-fidelity-completion-evidence/publication-delta.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS: exactly README.md and formalization.yaml changed at the two explicitly reviewed hashes; all other114 verified inputs unchanged.')
print('PASS: original statement, references, authorship, registry, approved notice, historical reports and historical audit preserved.')
