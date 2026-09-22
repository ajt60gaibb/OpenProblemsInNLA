#!/usr/bin/env python3
"""Independent static source, publication identity, and frozen boundary audit."""
from pathlib import Path
import hashlib, json, re, subprocess, datetime
HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent.parent
REPO = next(p for p in PROJECT.parents if (p/'problem_ids.json').exists())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
freeze = json.loads((PROJECT/'reviews/package-source-freeze.json').read_text())['source_sha256']
boundary = json.loads((PROJECT/'reviews/statement-freeze.json').read_text())['mathematical_boundary_sha256']
assert len(freeze) == 57 and len(boundary) == 4
assert all(sha(PROJECT/p) == h for p,h in freeze.items())
assert all(sha(PROJECT/p) == h for p,h in boundary.items())
vendor = json.loads((PROJECT/'reviews/IE21-DEPENDENCY.json').read_text())
vendored = {}
for p,h in vendor['source_sha256'].items():
    ref = vendor['source_commit']+':'+vendor['source_project']+'/'+p
    original = subprocess.check_output(['git','show',ref], cwd=REPO)
    assert hashlib.sha256(original).hexdigest() == h == sha(PROJECT/p)
    vendored[p] = h
assert len(vendored) == 31
readme = REPO/'linear-systems-and-elimination/IE-22/README.md'
manuscript = REPO/'references/colbrook-recovered-2026-09-11/manuscripts/IE-21-22.tex'
canonical = readme.read_text().split('## Problem statement\n\n')[1].split('\n## Connection')[0]
assert canonical in (PROJECT/'NUMERICAL_TARGETS.md').read_text()
assert '**Status:** Solved' in readme.read_text()

def code_only(text):
    out, pos, depth = [], 0, 0
    while pos < len(text):
        if text.startswith('/-',pos): depth += 1; pos += 2
        elif depth and text.startswith('-/',pos): depth -= 1; pos += 2
        elif depth: pos += 1
        elif text.startswith('--',pos):
            end = text.find('\n',pos)
            pos = len(text) if end < 0 else end
        else: out.append(text[pos]); pos += 1
    assert depth == 0
    return ''.join(out)

forbidden = re.compile(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern|run_tac|elab|macro|initialize)\b|#eval|import\s+Challenge')
math = sorted((PROJECT/'NLA').rglob('*.lean'))
assert len(math) == 47
hits = {str(p.relative_to(PROJECT)): forbidden.findall(code_only(p.read_text())) for p in math}
assert not any(hits.values()), hits
selected = json.loads((PROJECT/'comparator.json').read_text())['theorem_names']
solution = code_only((PROJECT/'Solution.lean').read_text())
assert re.findall(r'#assert_trust\s+kernel\s+(\S+)',solution) == selected
assert re.findall(r'#print\s+axioms\s+(\S+)',solution) == selected
assert 'set_option leancert.trust "kernel"' in solution
assert 'import LeanCert.Tactic.Verification' in solution
assert re.findall(r'\bsorry\b',code_only((PROJECT/'Challenge.lean').read_text())).__len__() == 20
assert not re.search(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}', '\n'.join((PROJECT/p).read_text() for p in freeze))
logs = list(HERE.glob('NLA__*.log'))
assert len(logs) == 47
assert all(': warning:' not in p.read_text() and ': error:' not in p.read_text() for p in logs)
auditlog = (HERE/'exact-types-and-axioms.log').read_text()
warnings = re.findall(r'warning: ([^\n]+)',auditlog)
assert all(w.startswith('Variable name `') and w.endswith('is not explicitly referenced.') for w in warnings)
receipt = {
 'phase': 'independent final correctness package inspection', 'timestamp_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'reviewer': 'ie22_final_correctness', 'ai_agent': True, 'nonauthor': True,
 'campaign_revision': subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip(),
 'source_package_freeze_sha256': sha(PROJECT/'reviews/package-source-freeze.json'),
 'proof_source_freeze_sha256': sha(PROJECT/'reviews/proof-source-freeze.json'),
 'preproof_statement_freeze_sha256': sha(PROJECT/'reviews/statement-freeze.json'),
 'source_files': freeze, 'unchanged_mathematical_boundary': boundary,
 'original_canonical_readme_sha256': sha(readme), 'full_retained_manuscript_sha256': sha(manuscript),
 'full_canonical_mathematical_statement_verbatim_in_inventory': True,
 'IE21_vendored_sources_match_git_objects_at_immutable_commit': vendor['source_commit'],
 'IE21_vendored_source_count': len(vendored), 'proof_module_count': len(math),
 'forbidden_code_hits': [], 'deliberate_reference_placeholder_count': 20,
 'selected_targets_with_explicit_authentic_kernel_trust_assertions': selected,
 'project_build_warning_count': 0, 'project_build_error_count': 0,
 'exact_type_audit_unused_binder_warning_count': len(warnings),
 'exact_type_audit_warning_disposition': 'All are nondependent proof binders retained verbatim from the frozen universal signatures; none is a hole or changed type. Original successful log retained; no source edits or linter suppression.',
 'new_contact_email_count': 0, 'canonical_status_unchanged': 'Solved',
 'upstream_source_lookup_limits': 'The local dependency cache contains compiled packages without full sources. A separate Mathlib source extraction was inspected for critical APIs but has no .git metadata; that inspection is not an authentication of cache objects. The pending Linux dependency receipt and kernel Comparator gate remain separate.',
 'lookup_attempts': ['Initial Mathlib and LeanCert source lookups inside the compiled dependency cache returned file-not-found.', 'A git revision query on the separate Mathlib source extraction returned not-a-git-repository.', 'Critical Mathlib API source text was then read from /private/tmp/mf21-mathlib-source-20260920; authentic LeanCert trust semantics were inspected in the retained IE21 Linux dependency source.']
}
(HERE/'package-inspection-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['campaign_revision','source_package_freeze_sha256','proof_module_count','IE21_vendored_source_count','project_build_warning_count','exact_type_audit_unused_binder_warning_count','canonical_status_unchanged']},indent=2))
