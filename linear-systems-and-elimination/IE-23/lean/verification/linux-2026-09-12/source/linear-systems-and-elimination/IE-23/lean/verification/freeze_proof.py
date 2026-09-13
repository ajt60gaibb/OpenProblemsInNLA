"""Freeze the completed IE23 author candidate without changing approved inputs.
Only this freeze and its completion note are excluded from the input set to
avoid circular hashes. Nested evidence manifests are always retained.
"""
from pathlib import Path
import datetime,hashlib,json,subprocess
P=Path(__file__).resolve().parents[1]
REPO=P.parents[2]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
f=json.loads((P/'reviews/statement-freeze.json').read_text())
start=json.loads((P/'verification/proof-start.json').read_text())
checks=json.loads((P/'verification/final-author/fresh-checks.json').read_text())
assert checks['status']=='PASS' and checks['fresh_commands']==10
assert checks['exact_exports']==8 and checks['axiom_audits']==16
for rel,digest in f['files'].items():assert sha(P/rel)==digest,rel
for rel,digest in start['records'].items():assert sha(P/rel)==digest,rel
for rel,digest in checks['source_inputs'].items():assert sha(P/rel)==digest,rel
for rel,digest in f['source_files'].items():
    raw=subprocess.check_output(['git','show',f['base']+':'+rel],cwd=REPO)
    assert sha(REPO/rel)==digest and (REPO/rel).read_bytes()==raw,rel

freeze=P/'reviews/proof-freeze.json'
completion=P/'reviews/proof-completion.md'
assert not freeze.exists() and not completion.exists()
files={}
for q in sorted(P.rglob('*')):
    if not q.is_file() or q in [freeze,completion]:continue
    rel=q.relative_to(P)
    if any(x in {'.lake','.verification','__pycache__','.git'} for x in rel.parts):continue
    files[str(rel)]={'sha256':sha(q),'bytes':q.stat().st_size}
data={'phase':'complete-author-proof-before-two-independent-final-referees',
 'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'source_commit':f['base'],'branch':f['branch'],'files':files,
 'source_files':f['source_files'],'project_input_count':len(files),'original_source_count':8,
 'statement_freeze_sha256':sha(P/'reviews/statement-freeze.json'),
 'unchanged_original_statement_project_count':32,
 'unchanged_original_statement_source_count':8,
 'config_supplement_sha256':sha(P/'reviews/statement-config-supplement.json'),
 'proof_start_sha256':sha(P/'verification/proof-start.json'),
 'statement_referee_approvals':{r:sha(P/r) for r in ['reviews/statement-referee-1.md','reviews/statement-referee-2.md']},
 'completed_exports':json.loads((P/'comparator.json').read_text())['theorem_names'],
 'fresh_check_receipt_sha256':sha(P/'verification/final-author/fresh-checks.json'),
 'scope':'All original contracts are complete; author fresh macOS checks only. Two independent final proof reviews and actual Linux remain pending.',
 'trust':'Explicit LeanCert kernel auditing, pure exact proof, standard three axioms; no interval certificate.',
 'dependency_objects':'Exact pinned MI22 source/build cache reused read-only; every project object freshly rebuilt in a separate prefix.',
 'local_Lake_invocation':False,'Linux_Comparator_run':False,
 'exclusions':'Generated .lake/.verification/__pycache__/.git paths, this outer proof freeze and its completion note only. All nested evidence manifests are included.'}
freeze.write_text(json.dumps(data,indent=2)+'\n')
completion.write_text(f'''# IE-23 completed proof handoff

**All eight approved exports are implemented and freshly compiled. Ready for
two independent final proof referees.** No publication, canonical promotion,
Linux success or independent final proof approval is claimed.

Project: `linear-systems-and-elimination/IE-23/lean`, isolated worktree
`/tmp/nla-lean-ie23-worktree`, branch `{f['branch']}`, unchanged upstream source
base `{f['base']}`. Git status contains only the untracked new Lean project.

The complete proof freeze is `reviews/proof-freeze.json`, SHA256
`{sha(freeze)}`, binding **{len(files)} project inputs and eight original
source files**. All 32 original statement inputs, all eight sources, the
exact Comparator selection and the additive supplement are unchanged. Every
source was checked against the actual base Git blob. Nested manifests are
included; only generated object/cache paths and the outer freeze/completion
pair are excluded.

| Bound object | SHA256 |
| --- | --- |
| Original statement freeze | `{sha(P/'reviews/statement-freeze.json')}` |
| Statement referee 1 | `{sha(P/'reviews/statement-referee-1.md')}` |
| Statement referee 2 | `{sha(P/'reviews/statement-referee-2.md')}` |
| Additive configuration supplement | `{sha(P/'reviews/statement-config-supplement.json')}` |
| Proof-start record, before the first proof edit | `{sha(P/'verification/proof-start.json')}` |
| Definitions | `{sha(P/'NLA/IE23/Definitions.lean')}` |
| Challenge | `{sha(P/'Challenge.lean')}` |
| Completed Proof | `{sha(P/'NLA/IE23/Proof.lean')}` |
| Completed Solution | `{sha(P/'Solution.lean')}` |
| Comparator configuration | `{sha(P/'comparator.json')}` |
| Fresh check receipt | `{sha(P/'verification/final-author/fresh-checks.json')}` |
| Actual dependency receipt | `{sha(P/'verification/final-author/actual-dependencies.json')}` |
| Actual inspection log | `{sha(P/'verification/final-author/verification-InspectProof.log')}` |

## Complete target and exact proof

The formalization negates the full original universal complex-matrix,
all-dimension and finite-real-p>2 uniqueness conjecture. Its p=4 witness is
exactly the source's matrix, without changed entries. All denominators,
Euclidean norms, real powers, matrix inverse, rank, suprema and global
competitors retain their actual Mathlib meanings. No additional assumptions
hide the nonemptiness, boundedness, invertibility or numerical conclusions.

`Norms.lean` proves the generic induced-norm semantics for every original
domain. The coordinate p-norm bound and finite matrix-entry sum give an
explicit finite upper bound; the actual `isLUB_csSup` and `le_csSup`/`csSup_le`
rules handle the supremum. Zero inputs are addressed separately. Matrix
products certify the actual inverse, rank and both right inverses.

The fourth-root comparison reduces to `(a²−b²)²≥0`, with actual real-power and
nonnegative-square bridges. Exact complex action identities yield both
attained ratios. For every complex right inverse Y, its actual right-inverse
equation forces Yz=(t,1−t,−1−t), and the true squared Euclidean norm is
2+3|t|². This supplies a lower bound for every admissible competitor. The
two distinct feasible matrices attain the same norm c=√(√2), are both global
minimizers, and give a genuine least feasible value. Their equality refutes
the complete original strict uniqueness claim.

`PROOF_MAP.md` gives the complete source/module/contract correspondence. The
source's all-p extensions and complete minimizer classification remain
outside the eight exports, as stated and approved before proof. The original
mathematical resolution is credited to Matthew J. Colbrook, the matrix to
Dokmanić and Gribonval, and the AI-assisted formalization to George
Stepaniants, Department of Computing and Mathematical Sciences, California
Institute of Technology, Pasadena, California, USA. No email is added.

## What actually ran

The author ran **ten fresh commands**, all exit zero: Definitions, Norms,
Matrices, FourthPower, Actions, Minimizers, Proof, Solution, the separately
isolated Challenge and the actual-term inspector. The only warnings were the
eight intentional Challenge placeholders; no completed proof imports
Challenge. All eight normalized export signatures match exactly. Sixteen
internal/public LeanCert `#assert_trust kernel` and transitive axiom reports
show only `propext`, `Classical.choice`, and `Quot.sound`.

The actual proof traversal reaches **93 project declarations** and requires
**38 material dependencies**, including actual Euclidean norm, real powers,
rank, inverse, supremum and every counterexample/minimality bridge. All ten
dependency sources are clean at their exact manifest revisions. Source
inputs and all frozen statement/configuration/source bytes were checked
again after completion. Raw commands, hashes, object paths, term prints and
trust reports are retained under `verification/final-author/`.

LeanCert's approved role here is **explicit kernel trust auditing of a pure
exact proof**. There is no artificial interval certificate, numerical grid,
approximate spectral computation, admission, custom axiom or native proof.
The exact symbolic proof eliminates all interval computation.

Because the shared disk has less than one gigabyte free, the run reused
matching private MI-22 dependency objects **read-only**, as explicitly
authorized. Every IE-23 project module was compiled into a new separate
prefix, and all earlier project objects were excluded from `LEAN_PATH`.
Lean is 4.33.1 on macOS; this was **not a local Lake invocation, full
dependency-source rebuild, independent referee run, or Linux Comparator
execution**. The unchanged Lake configuration registers Solution; a normal
checkout's explicit proof command is `lake build Solution`, while the
deliberate default remains Challenge.

The statement-stage README and source plan remain historically frozen;
publication packaging must archive/refresh the README and describe the
historical documents accurately. Both independent final referees, actual
Linux kernel/Comparator and controls, truthful v0.4 metadata, and independent
publication review remain necessary. No canonical file, ID, status, commit,
push or PR was changed by this implementation task.
''')
print(json.dumps({'status':'FROZEN','project_inputs':len(files),'original_sources':8,
 'proof_freeze_sha256':sha(freeze),'completion_sha256':sha(completion),
 'Proof_sha256':sha(P/'NLA/IE23/Proof.lean'),'Solution_sha256':sha(P/'Solution.lean')},indent=2))
