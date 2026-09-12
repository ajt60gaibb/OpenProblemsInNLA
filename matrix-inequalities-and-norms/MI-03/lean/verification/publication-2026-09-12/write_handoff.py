from pathlib import Path
import ast, hashlib, json

repo=Path('/tmp/nla-lean-mi03-worktree')
p=repo/'matrix-inequalities-and-norms/MI-03/lean/verification/publication-2026-09-12'
x=json.loads((p/'integrity.json').read_text())
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
for f in p.glob('*.py'): ast.parse(f.read_text())
report=f'''# MI-03 publication preparation - 12 September 2026

**PASS: ready for independent parent publication review.** Prepared by
`/root/formal_review_standards`. This is a publication handoff, not an additional
mathematical proof review or a new Linux run. No publication commit, push or PR
was made. Parent review is the remaining publication gate.

## Verified result and scope

The unchanged proof at `{x['verified_revision']}` passed actual
[Linux run 34722618003](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34722618003).
The accepted [operational report](../linux-2026-09-12/OPERATIONAL-REVIEW.md)
has SHA256 `0c582ae4b9271ce89cd9484a45d380f3cfa8cab60595a7986debcaa67c084e30`.
Its outer manifest is `ecbdf4f208c72dd016442ca7dba5fd925b5c51286719454e5a58563460a610d9`.
All eight Comparator exports and Lean default-kernel replay passed with exactly
the standard three foundational axioms. Sixteen internal/public axiom reports
and both real standalone/per-project isolation/rejection suites were audited.
The nested Bubblewrap executable was denied UID-map creation before its inner
write; no execution of that inner write or general security guarantee is claimed.

Only MI-03 is promoted from Solved to Lean verified in the prepared working tree.
The full original assertion concerns every odd k at least three, every positive
matrix dimension and every complex contraction tuple. The proof establishes the
stronger all-k-at-least-two result: k/4 is **IsLeast of the entire set of
admissible nonnegative constants**, and its actual real infimum. Principal CFC
moduli, genuine Euclidean operator norms, exact roots and full matrix sums are
retained. The universal upper bound is proved internally. Additional source
three-dimensional Hermitian extremizers and rank classification are explicitly
outside the exports; the complete original target is covered. LeanCert supplies
explicit kernel trust auditing of an exact proof, with no interval certificate.

George Stepaniants is visibly credited for the AI-assisted formalization with
his Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA affiliation. No email is added. Matthew J.
Colbrook retains the mathematical proof/result credit; Jean-Christophe Bourin
and Eun-Young Lee retain the conjecture and prior-bound credit. All original
source attribution and informal reviews are preserved as historical records.

The operational reviewer and this publication preparer are also statement
referee 1 and final proof referee 1. These overlapping roles are explicitly
disclosed in the canonical page, project guide, manifest and resolution entry;
they do not create a third mathematical referee. Both independent final proof
reviewers are distinct from the proof author `/root`. No external human review,
official Tau Ceti endorsement, source-author endorsement or priority is claimed.

## Integration and preservation

A fresh query of actual upstream main returned
`{x['upstream_base']}`. The existing tracking ref already matched it.
The normal conflict-free merge `{x['integration_commit']}` has exactly the
verified candidate and that upstream revision as parents. Its author and
committer are George Stepaniants, with **both email fields entirely empty**.
This authorized integration commit is the only commit made in this task.
There has been no history rewrite or push. The actual verified revision remains
the original candidate; no verification of new publication wrappers is invented.

The [executable integrity check](finish.py) and [bound result](integrity.json)
confirm:

- **171 of 173** verified inputs are byte-identical. Only the current project
  README and formalization.yaml change, and both exact prior wrappers are
  archived under [archive/](archive/). All mathematical files, statements,
  configurations, ten pins and prior referee/evidence inputs remain unchanged.
- All **100 non-README proof-freeze inputs** remain identical. The historical
  statement-stage README archive still matches its frozen hash.
- All **304 Linux evidence files** are byte-identical: **303 bound files plus
  the exact outer manifest**. Every nested manifest is included. All eight
  original canonical/source snapshots remain bound and retained. The original
  manuscript and informal proof/review sources are unchanged in the worktree;
  only the canonical README and its generated TeX/PDF gain the verification notice.
- All **216 other canonical pages**, all **217 permanent IDs**, every other
  RESOLVED block, and the complete original MI-03 statement/reference/history
  tail are unchanged. All **11** earlier upstream Lean verifications are retained.
- All **{x['unchanged_upstream_file_count']}** upstream files outside the seven intended existing
  publication/index files match their original Git blob bytes. Shared tools,
  source lock, workflow, renderer and registry are unchanged.
- Exactly nine tracked files differ from the integration commit: the canonical
  README/TeX/PDF, two project wrappers, RESOLVED and three generated indexes.
  The retained Linux and publication evidence directories are additional inputs.
- Exactly five manifest fields change: status.scope, review.status,
  review.notes and review.linux_verification.status/note. All eight declaration
  mappings, report hashes, source/automation/attribution fields and other
  schema content are preserved.

Both permanent-ID validators pass against `origin/main` and `nla-upstream/main`.
Required catalog generation, all **17** ID tests, all-canonical math formatting,
the actual pinned v0.4 schema and eight-export Comparator coverage pass. Final
counts on this integrated branch are **12 Lean verified, 78 Solved, 55 Open and
72 Partially resolved**. These are this branch's counts, not unmerged PRs elsewhere.

## Documents and remaining review

The unchanged repository renderer regenerated the canonical TeX and PDF. All
**three final pages** were individually displayed and visually inspected:
page 1 contains attribution, verified scope, all exports and observed execution;
page 2 contains exact pins, reproduction commands and the unchanged full target;
page 3 preserves the source references and historical search note. There is no
clipping, overlap, missing glyph or unreadable equation. The dedicated reference
page is selected by the existing renderer. Both rendered passes succeeded.

An initial whitespace check caught new trailing spaces on the status line;
they were removed before the final render and final page inspection. A later
supplementary text-extraction diagnostic initially missed California because
the PDF wraps it as Cali- / fornia. The original script, failure record and raw
text are retained. The corrected diagnostic normalizes line-end hyphenation and
whitespace only; actual PDF bytes and all preservation assertions are unchanged.

PDF SHA256: `{x['changed_file_sha256']['matrix-inequalities-and-norms/MI-03/problem.pdf']}`.
Canonical README SHA256: `{x['changed_file_sha256']['matrix-inequalities-and-norms/MI-03/README.md']}`.
Manifest SHA256: `{x['changed_file_sha256']['matrix-inequalities-and-norms/MI-03/lean/formalization.yaml']}`.
Integrity record SHA256: `{sha(p/'integrity.json')}`.

The parent should independently inspect the diff, wrapper claims and all three
PDF pages before its authorized publication commit/push/PR. No mathematical
source re-elaboration or second Linux run is necessary for these publication
edits: the complete immutable proof/evidence binding is preserved.
'''
(p/'PUBLICATION-HANDOFF.md').write_text(report)
(p/'write_handoff.py').write_bytes(Path(__file__).read_bytes())
outer=p/'EVIDENCE-MANIFEST.json'
files={str(f.relative_to(p)):{'bytes':f.stat().st_size,'sha256':sha(f)} for f in sorted(p.rglob('*')) if f.is_file() and f!=outer}
outer.write_text(json.dumps({'purpose':'MI-03 publication preparation; independent parent publication review pending','file_count':len(files),'files':files},indent=2)+'\n')
assert {str(f.relative_to(p)) for f in p.rglob('*') if f.is_file() and f!=outer} == set(files)
print(json.dumps({'handoff_sha256':sha(p/'PUBLICATION-HANDOFF.md'),'integrity_sha256':sha(p/'integrity.json'),
                  'publication_evidence_manifest_sha256':sha(outer),'publication_bound_files':len(files),
                  'publication_total_including_outer':len(files)+1,'pdf_sha256':x['changed_file_sha256']['matrix-inequalities-and-norms/MI-03/problem.pdf'],
                  'integration_commit':x['integration_commit']},indent=2))
