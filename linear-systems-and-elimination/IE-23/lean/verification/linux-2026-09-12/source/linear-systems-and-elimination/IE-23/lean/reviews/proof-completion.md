# IE-23 completed proof handoff

**All eight approved exports are implemented and freshly compiled. Ready for
two independent final proof referees.** No publication, canonical promotion,
Linux success or independent final proof approval is claimed.

Project: `linear-systems-and-elimination/IE-23/lean`, isolated worktree
`/tmp/nla-lean-ie23-worktree`, branch `codex/lean-ie23-induced-norm-nonuniqueness`, unchanged upstream source
base `f41f1f9ffa2171550d4bb795862c6170c4f26070`. Git status contains only the untracked new Lean project.

The complete proof freeze is `reviews/proof-freeze.json`, SHA256
`8ed8f46ea66c9e420156d99840e4e24e78cf8207a9e415cc7c26f6f9739e5fe8`, binding **104 project inputs and eight original
source files**. All 32 original statement inputs, all eight sources, the
exact Comparator selection and the additive supplement are unchanged. Every
source was checked against the actual base Git blob. Nested manifests are
included; only generated object/cache paths and the outer freeze/completion
pair are excluded.

| Bound object | SHA256 |
| --- | --- |
| Original statement freeze | `6e9b62ab46974a54204ba7636ec83209bd102fd322794709c83a46df85d417f1` |
| Statement referee 1 | `d2f3669ada22f985ce66681a1b763d0fc722d1938b9c2a35b27792f7fc418270` |
| Statement referee 2 | `dda8d5d5dc194371818ecef9fa4e1a20d52dbadc7b8f998dff4a815cfbd4f758` |
| Additive configuration supplement | `dafd6645aa017c543dd4eb9f60633b47a2035f090d58955525a3d6c41156141a` |
| Proof-start record, before the first proof edit | `7380aff57e428652e86548d6f1ad535a175d1fc8b1da1b3009092bdd6a868fec` |
| Definitions | `1af986f21059b5b9862decf09366d3ea8dba0c965a5b8550b8d9a0fcc41af33f` |
| Challenge | `faf9ae407be25d4fded2737a4dd4ef41a329a3cc25e194c0d06159b6a788319d` |
| Completed Proof | `2224a18d89621ef254e3a606b8e711e1576e1bb4e312365a9b4b4706eddc9ca6` |
| Completed Solution | `ce642354744645994d4462dff367595ba441781d19ed57a2dd99fe2303e5c671` |
| Comparator configuration | `8a02cee6a555e2bd658cb2daa22bfaba515027d787d570846aae21aaac2e26cb` |
| Fresh check receipt | `028fdde56de34469183a5f5c64424f1780acb50508402af04c514b154c943203` |
| Actual dependency receipt | `5fd38c8ead48804917370daa20bc84ba0e9ab94b69f83679ac5411fb9865feb8` |
| Actual inspection log | `dae1e71c3af75476193702a34d506804587907a079f81e675c38597b9b8b197d` |

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
