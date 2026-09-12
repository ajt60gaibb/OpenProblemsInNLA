from pathlib import Path
import ast, hashlib, json

project=Path('/tmp/nla-lean-ie23-worktree/linear-systems-and-elimination/IE-23/lean')
p=project/'verification/linux-candidate-2026-09-12'
x=json.loads((p/'packaging-record.json').read_text())
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
report=f'''# IE-23 completed-proof Linux candidate - 12 September 2026

**PASS: candidate documentation and preservation checks are ready for parent
review.** Actual Linux verification remains pending. Prepared by
`/root/formal_review_standards`, which did not author IE-23's statements or
proof and is not either independent final mathematical referee. This task
performed packaging and integrity checks only, with no new Lean/Lake invocation,
dependency download/build, canonical edit, commit, push or PR.

## Completed mathematical scope and accepted reviews

The refreshed [guide](../../README.md) and actual v0.4
[manifest](../../formalization.yaml) describe all eight completed exports,
their original-target correspondence, actual local checks and remaining gates.
The final result negates the entire original universal uniqueness assertion
for all original dimensions, full-row-rank complex matrices, finite real p>2,
and distinct complex right inverses. The unchanged source matrices at m=2,
n=3 and p=4 provide two different global minimizers with norm sqrt(sqrt(2)).
The generic actual nonzero-input supremum is proved nonempty and bounded,
with its genuine least-upper-bound property. Matrix rank, Moore-Penrose inverse,
real powers and Euclidean norms retain their real library meanings. Every
complex right-inverse competitor is covered by the actual action identity,
yielding global minimality and IsLeast of the complete feasible norm set.

The stronger source all-p formulas, complete classifications, higher-dimensional
families, smallest-dimension assertion, endpoints and separate product objective
remain outside the exports. No unproved source inequality or numerical oracle is
assumed. LeanCert's explicit role is **kernel trust auditing of a pure exact
proof**; there is no numerical interval certificate. The exact p=4 reduction
avoids approximate norm calculations, spectral enclosures and subdivision.

Both independent statement approvals, including the exact additive Comparator
supplement, preceded implementation. Both independent final reviews are accepted:

| Independent reviewer | Final report SHA256 | Evidence manifest SHA256 |
| --- | --- | --- |
| `/root/solved_statement_inventory` | `4aded9a6adfc4723941bae2ac8c4ae0c1ad4bdef7136dd3a285068ae1f68d4d2` | `bb232d4c5a8c2a8fb75238547cbc9646a99ab8f3904286152f52963140132748` |
| `/root` | `0b6f2f6ed1aa4505da7ceb63d33470822914820904a4b0fee309f69ba314c008` | `020a62b026a9d00b6e41b50feefd468979d87a74e3384a688a1bb449b49a2847` |

Their manifests bind 35 and 23 files respectively, including the corresponding
report through its relative parent path. Every internal evidence file and each
bound report were checked against these exact hashes. No nested manifest was
omitted. Both statement reports and their separate complete evidence manifests
were also rehashed. The implementing agent is `/root/leancert_examples`;
the coordinator's reviewer role is independent of that implementation. No extra
mathematical referee is inferred from the packaging role.

The author and each final referee completed ten actual fresh macOS Lean commands.
All sixteen internal/public kernel assertions and transitive axiom reports use
only `propext`, `Classical.choice` and `Quot.sound`. Each inspection reaches
93 project declarations. The independent reviewers require 40 and 28 material
dependencies respectively; the latter also performs twelve kernel assertions.
Exact matching MI-22 dependency objects were reused read-only, with new private
IE-23 prefixes excluding all old project objects. These were direct elaborations,
not local Lake runs, full dependency-source rebuilds or Linux Comparator results.

## Immutable inputs, source and privacy

Proof freeze `8ed8f46ea66c9e420156d99840e4e24e78cf8207a9e415cc7c26f6f9739e5fe8`
binds 104 project inputs and eight original sources. Only its live README changes;
all **103 non-README inputs** remain byte-identical. The exact historical README,
SHA256 `1c709941dd5c19fbe90d157a4777f7dcadc43e365f4769d980a0bad283b3d5ac`,
is archived as [README.statement.md](README.statement.md). The frozen numerical
targets, source correspondence, proof map and phase-specific reports remain
historical documents dated 12 September 2026. The live guide accurately
describes the later approvals and their limits without editing those records.

Of all **166 preexisting project files**, exactly **165** remain unchanged;
the sole changed file is README.md. The new formalization.yaml and this packaging
evidence are additive. All eight original sources and retained source snapshots,
both final evidence sets, four review reports, actual Comparator and the exact
additive supplement remain unchanged. Comparator selects precisely eight theorem
names, no definition exceptions and the standard-three axiom whitelist.

All ten dependency sources were independently rechecked read-only at their exact
clean Git revisions. No build artifacts were recreated, copied or deleted. The
complete [packaging record](packaging-record.json) binds the prior inputs, reviews,
current wrapper hashes and source identity. The source baseline remains
`{x['source_base']}`; the shared upstream tracking ref had independently advanced
to `{x['current_upstream_tracking_reference']}` during packaging. No integration
was attempted in this task and no status-count claim is made about current main.

Every tracked file and all **217 canonical pages/IDs** remain identical to this
worktree's original base. Canonical IE-23 stays **Solved**. Required validators
against origin/main and the current nla-upstream/main ref, index regeneration,
all **17** permanent-ID tests, and the pinned actual v0.4 schema with all eight
Comparator declarations passed. Index regeneration produced no tracked change.

George Stepaniants receives formalization authorship with the full Department
of Computing and Mathematical Sciences, California Institute of Technology,
Pasadena, California, USA affiliation and AI assistance. No email is added.
Matthew J. Colbrook retains mathematical resolution credit; Dokmanić and
Gribonval retain the underlying example and original question. Source-author
endorsement, external human peer review, official Tau Ceti endorsement and
historical priority are not claimed.

## Remaining gates and reproducibility note

The guide supplies normal `lake build Solution` and future immutable-revision
Linux bootstrap/selftest/verify commands. An initial packaging assertion caught
a proposed unsupported environment override in the fixed-path historical proof
runner before either current wrapper was written. The discarded script and
failure record are retained; the final guide correctly describes these as
historical replay drivers requiring isolated frozen inputs and their recorded
paths. No proof or test result was fabricated, and no completed proof check was
rerun. The eight deliberate Challenge placeholders remain separate from Solution.

README SHA256: `{x['metadata_sha256']['README.md']}`.
formalization.yaml SHA256: `{x['metadata_sha256']['formalization.yaml']}`.
Packaging record SHA256: `{sha(p/'packaging-record.json')}`.

Parent review of these exact wrapper claims and preservation evidence is next.
Only afterward should the candidate be committed and sent to the actual Linux
checker. Its observed Comparator/default-kernel/control results must then receive
an independent operational audit and publication review before canonical promotion.
No project-specific immutable proof revision or Linux PASS is asserted here.
'''
(p/'CANDIDATE-HANDOFF.md').write_text(report)
(p/'seal.py').write_bytes(Path(__file__).read_bytes())
for f in p.glob('*.py'):ast.parse(f.read_text())
outer=p/'EVIDENCE-MANIFEST.json'
files={str(f.relative_to(p)):{'bytes':f.stat().st_size,'sha256':sha(f)} for f in sorted(p.rglob('*')) if f.is_file() and f!=outer}
metadata={name:{'bytes':(project/name).stat().st_size,'sha256':sha(project/name)} for name in ['README.md','formalization.yaml']}
outer.write_text(json.dumps({'purpose':'IE-23 reviewed completed-proof candidate packaging; actual Linux and parent review pending',
 'file_count':len(files),'files':files,'current_metadata_relative_to_project':metadata,
 'inventory_rule':'Every candidate-evidence file is included; only this exact outer manifest excludes itself. Nested manifests are not filtered by basename.'},indent=2)+'\n')
assert {str(f.relative_to(p)) for f in p.rglob('*') if f.is_file() and f!=outer}==set(files)
print(json.dumps({'handoff_sha256':sha(p/'CANDIDATE-HANDOFF.md'),'record_sha256':sha(p/'packaging-record.json'),
 'manifest_sha256':sha(outer),'bound_evidence_files':len(files),'evidence_files_including_outer':len(files)+1,
 'additional_bound_metadata_files':len(metadata)},indent=2))
